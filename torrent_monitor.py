#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
torrent_monitor V2.0
protocol_version: 2.0
单文件：支持 CLI / PyQt6‑GUI
流程：
1.加载配置校验protocol_version=2.0
2.抓取全部search‑terms，auto/manual全部过滤入库，status=pending
3.GUI模式：逐个弹出manual组QDialog窗口，收集用户勾选种子info_hash集合（暂不推送）
4.合并【auto全部命中】+【GUI手动勾选】作为待推送总列表，统一批量提交qBittorrent
5.统一写数据库推送状态与日志
CLI模式：mode=manual的搜索项打印警告，不做人工选择。

依赖：
pip install pyyaml requests beautifulsoup4 pyqt6
用法：
# CLI命令行模式
python torrent_monitor.py --config config.yaml
# GUI图形界面模式
python torrent_monitor.py --gui --config config.yaml
# dry‑run只抓取入库，不推送
python torrent_monitor.py --gui --dry-run --config config.yaml
"""
from __future__ import annotations
import argparse
import hashlib
import logging
import re
import sqlite3
import sys
import time
from datetime import datetime, timedelta
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple, Set

try:
    from PyQt6.QtWidgets import (QApplication, QDialog, QTableWidget, QTableWidgetItem,
                                 QPushButton, QVBoxLayout, QCheckBox, QHeaderView,
                                 QMessageBox)
    from PyQt6.QtCore import Qt
    HAVE_GUI = True
except ImportError:
    HAVE_GUI = False

import requests
import yaml
from bs4 import BeautifulSoup

SCRIPT_VERSION = "2.0"
REQUIRED_PROTOCOL_VERSION = "2.0"

LOG = logging.getLogger("torrent_monitor")
DEFAULT_USER_AGENT = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/124.0 Safari/537.36"
)
FUTURE_TOLERANCE = timedelta(hours=12)
SIZE_RE = re.compile(r"([\d.,]+)\s*(KiB|MiB|GiB|TiB|KB|MB|GB|TB|B)(?!\w)", re.I)
RE_TODAY = re.compile(r"^Today\s+(\d{1,2}):(\d{2})", re.I)
RE_YDAY = re.compile(r"^Y-day\s+(\d{1,2}):(\d{2})", re.I)
RE_MDHM = re.compile(r"^(\d{1,2})-(\d{1,2})\s+(\d{1,2}):(\d{2})")
RE_MD = re.compile(r"^(\d{1,2})-(\d{1,2})$")
RE_FULL = re.compile(r"^(\d{4})-(\d{1,2})-(\d{1,2})")

SIZE_FACTORS = {
    "B": 1,
    "KB": 1000,
    "MB": 1000 ** 2,
    "GB": 1000 ** 3,
    "TB": 1000 ** 4,
    "KIB": 1024,
    "MIB": 1024 ** 2,
    "GIB": 1024 ** 3,
    "TIB": 1024 ** 4,
}

# ---------------------------------------------------------------------------
# 通用工具
# ---------------------------------------------------------------------------
def now_iso() -> str:
    return datetime.now().replace(microsecond=0).isoformat()

def resolve_path(value: str, base_dir: Path) -> Path:
    p = Path(value).expanduser()
    return p if p.is_absolute() else (base_dir / p).resolve()

def load_config(path: Path) -> Dict[str, Any]:
    with path.open("r", encoding="utf-8") as f:
        cfg = yaml.safe_load(f) or {}
    if not isinstance(cfg, dict):
        raise ValueError("配置文件顶层必须是映射（key: value）结构")

    proto_ver = cfg.get("protocol_version")
    if proto_ver != REQUIRED_PROTOCOL_VERSION:
        raise ValueError(
            f"配置协议版本不匹配！脚本需要 protocol_version={REQUIRED_PROTOCOL_VERSION}，"
            f"当前配置为 {proto_ver}，请更新 config.yaml"
        )

    for section in ("global", "database", "qbittorrent", "logging"):
        cfg.setdefault(section, {})
    terms = cfg.get("search-terms")
    if not isinstance(terms, list) or not terms:
        raise ValueError("配置缺少非空列表 'search-terms'")
    for i, term in enumerate(terms):
        if not isinstance(term, dict):
            raise ValueError(f"search-terms[{i}] 必须是映射结构")
        if not term.get("url"):
            raise ValueError(f"search-terms[{i}] 缺少 'url'")
        term.setdefault("mode", "auto")
    return cfg

def term_filters(term: Dict[str, Any]) -> Dict[str, Any]:
    size_cfg = term.get("size") or {}
    max_mb = term.get("max_size_mb", size_cfg.get("max_mb"))
    return {
        "title_contains": term.get("title_contains") or [],
        "size": {"max_mb": max_mb},
        "max_age_days": term.get("max_age_days"),
    }

def setup_logging(cfg: Dict[str, Any], base_dir: Path) -> None:
    level_name = str(cfg.get("level", "INFO")).upper()
    level = getattr(logging, level_name, logging.INFO)
    LOG.setLevel(level)
    LOG.handlers.clear()
    fmt = logging.Formatter("%(asctime)s [%(levelname)s] %(message)s", "%Y-%m-%d %H:%M:%S")
    sh = logging.StreamHandler(sys.stdout)
    sh.setFormatter(fmt)
    LOG.addHandler(sh)
    log_file = cfg.get("file")
    if log_file:
        p = resolve_path(str(log_file), base_dir)
        p.parent.mkdir(parents=True, exist_ok=True)
        fh = logging.FileHandler(p, encoding="utf-8")
        fh.setFormatter(fmt)
        LOG.addHandler(fh)

# ---------------------------------------------------------------------------
# 解析：大小 / 日期 / magnet
# ---------------------------------------------------------------------------
def parse_size(text: str) -> Optional[int]:
    m = SIZE_RE.search(text.replace("\xa0", " ").strip())
    if not m:
        return None
    num_str = m.group(1)
    if "." in num_str and "," in num_str:
        num_str = num_str.replace(",", "")
    elif "," in num_str:
        groups = num_str.split(",")
        num_str = num_str.replace(",", "") if all(len(g) == 3 for g in groups[1:]) else num_str.replace(",", ".")
    try:
        value = float(num_str)
    except ValueError:
        return None
    factor = SIZE_FACTORS[m.group(2).upper()]
    return int(value * factor)

def parse_tpb_date(text: str, now: datetime) -> Optional[datetime]:
    s = text.replace("\xa0", " ").strip()
    m = RE_TODAY.match(s)
    if m:
        return now.replace(hour=int(m.group(1)), minute=int(m.group(2)), second=0, microsecond=0)
    m = RE_YDAY.match(s)
    if m:
        return (now - timedelta(days=1)).replace(
            hour=int(m.group(1)), minute=int(m.group(2)), second=0, microsecond=0
        )
    m = RE_MDHM.match(s)
    if m:
        month, day, hour, minute = map(int, m.groups())
        try:
            d = datetime(now.year, month, day, hour, minute)
        except ValueError:
            return None
        if d > now + timedelta(days=1):
            try:
                d = d.replace(year=now.year - 1)
            except ValueError:
                return None
        return d
    m = RE_MD.match(s)
    if m:
        month, day = map(int, m.groups())
        try:
            d = datetime(now.year, month, day)
        except ValueError:
            return None
        if d > now + timedelta(days=1):
            d = d.replace(year=now.year - 1)
        return d
    m = RE_FULL.match(s)
    if m:
        year, month, day = map(int, m.groups())
        try:
            return datetime(year, month, day)
        except ValueError:
            return None
    return None

def info_hash_from_magnet(magnet: str) -> str:
    m = re.search(r"btih:([0-9a-fA-F]{40}|[A-Za-z2-7]{32})", magnet)
    if m:
        return m.group(1).lower()
    return "sha1:" + hashlib.sha1(magnet.encode("utf-8")).hexdigest()

# ---------------------------------------------------------------------------
# 抓取 + 页面解析
# ---------------------------------------------------------------------------
def fetch_html(url: str, cfg: Dict[str, Any]) -> str:
    headers = {"User-Agent": cfg.get("user_agent") or DEFAULT_USER_AGENT}
    timeout = float(cfg.get("timeout_seconds", 25))
    retries = int(cfg.get("retries", 2))
    last_error: Optional[Exception] = None
    session = requests.Session()
    session.trust_env = bool(cfg.get("trust_env", True))
    for attempt in range(retries + 1):
        try:
            LOG.info("抓取页面 %s（第 %d/%d 次）", url, attempt + 1, retries + 1)
            resp = session.get(url, headers=headers, timeout=timeout)
            resp.raise_for_status()
            resp.encoding = resp.apparent_encoding or "utf-8"
            return resp.text
        except Exception as exc:
            last_error = exc
            LOG.warning("抓取失败：%s", exc)
            if attempt < retries:
                time.sleep(1.5 * (attempt + 1))
    raise RuntimeError(f"抓取页面失败（已重试 {retries} 次）：{last_error}")

def parse_page(html: str, now: datetime) -> List[Dict[str, Any]]:
    soup = BeautifulSoup(html, "html.parser")
    results: List[Dict[str, Any]] = []
    for tr in soup.find_all("tr"):
        links = [a for a in tr.find_all("a", href=True)]
        title_a = next(
            (a for a in links if "/torrent/" in a["href"] and a.get("title", "").startswith("Details for")),
            None,
        )
        if title_a is None:
            title_a = next((a for a in links if "/torrent/" in a["href"]), None)
        if title_a is None:
            continue
        magnet = next((a["href"] for a in links if a["href"].startswith("magnet:?")), None)
        if not magnet:
            continue
        title = title_a.get_text(" ", strip=True) or title_a.get("title", "").replace("Details for ", "", 1).strip()
        tds = tr.find_all("td", recursive=False)
        category = None
        cat_a = next((a for a in links if "/browse/" in a["href"]), None)
        if cat_a:
            category = cat_a.get_text(" ", strip=True) or None
        uploader = None
        for a in links:
            if "/user/" in a["href"] and a.get_text(strip=True):
                uploader = a.get_text(strip=True)
                break
        published_raw, published_dt = None, None
        for td in tds:
            txt = td.get_text(" ", strip=True).replace("\xa0", " ")
            parsed = parse_tpb_date(txt, now)
            if parsed is not None:
                published_raw, published_dt = txt, parsed
                break
        size_text, size_bytes = None, None
        for td in tds:
            txt = td.get_text(" ", strip=True).replace("\xa0", " ")
            m = SIZE_RE.search(txt)
            if m:
                size_text = txt
                size_bytes = parse_size(txt)
                break
        seeders = leechers = None
        if size_text is not None:
            size_idx = next(
                (i for i, td in enumerate(tds) if size_text in td.get_text(" ", strip=True).replace("\xa0", " ")),
                None,
            )
            if size_idx is not None:
                nums = []
                for td in tds[size_idx + 1:]:
                    txt = td.get_text(strip=True).replace("\xa0", "")
                    if re.fullmatch(r"\d+", txt):
                        nums.append(int(txt))
                    if len(nums) == 2:
                        break
                seeders = nums[0] if len(nums) > 0 else None
                leechers = nums[1] if len(nums) > 1 else None
        results.append(
            {
                "info_hash": info_hash_from_magnet(magnet),
                "title": title,
                "category": category,
                "torrent_url": title_a["href"],
                "magnet": magnet,
                "published_at": published_dt.replace(microsecond=0).isoformat() if published_dt else None,
                "published_raw": published_raw,
                "size_bytes": size_bytes,
                "size_text": size_text,
                "seeders": seeders,
                "leechers": leechers,
                "uploader": uploader,
            }
        )
    return results

def passes_filters(
    item: Dict[str, Any], filters: Dict[str, Any], now: datetime
) -> Tuple[bool, str]:
    keywords = [str(k).strip().lower() for k in (filters.get("title_contains") or []) if str(k).strip()]
    title_l = (item.get("title") or "").lower()
    for kw in keywords:
        if kw not in title_l:
            return False, f"标题不含关键字 '{kw}'"
    size_cfg = filters.get("size") or {}
    max_mb = size_cfg.get("max_mb")
    if max_mb is not None:
        if item.get("size_bytes") is None:
            return False, "无法解析大小"
        limit = float(max_mb) * 1024 * 1024
        if item["size_bytes"] > limit:
            return False, f"大小 {item.get('size_text')} 超过上限 {max_mb} MiB"
    max_age_days = filters.get("max_age_days")
    if max_age_days is not None:
        if not item.get("published_at"):
            return False, "无法解析发布日期"
        published = datetime.fromisoformat(item["published_at"])
        age = now - published
        if age < -FUTURE_TOLERANCE:
            return False, "发布日期异常（在未来）"
        if age > timedelta(days=float(max_age_days)):
            return False, f"发布日期距今超过 {max_age_days} 天"
    return True, "ok"

# ---------------------------------------------------------------------------
# SQLite
# ---------------------------------------------------------------------------
def init_db(db_path: Path) -> sqlite3.Connection:
    db_path.parent.mkdir(parents=True, exist_ok=True)
    conn = sqlite3.connect(db_path)
    conn.row_factory = sqlite3.Row
    conn.executescript(
        """
        CREATE TABLE IF NOT EXISTS torrents (
            info_hash     TEXT PRIMARY KEY,
            title         TEXT NOT NULL,
            category      TEXT,
            torrent_url   TEXT,
            magnet        TEXT NOT NULL,
            published_at  TEXT,
            published_raw TEXT,
            size_bytes    INTEGER,
            size_text     TEXT,
            seeders       INTEGER,
            leechers      INTEGER,
            uploader      TEXT,
            first_seen    TEXT NOT NULL,
            last_seen     TEXT NOT NULL,
            push_status   TEXT NOT NULL DEFAULT 'pending',
            push_attempts INTEGER NOT NULL DEFAULT 0,
            last_push_at  TEXT,
            push_error    TEXT
        );
        CREATE INDEX IF NOT EXISTS idx_torrents_push_status ON torrents(push_status);
        CREATE TABLE IF NOT EXISTS push_log (
            id           INTEGER PRIMARY KEY AUTOINCREMENT,
            info_hash    TEXT NOT NULL,
            title        TEXT,
            attempted_at TEXT NOT NULL,
            success      INTEGER NOT NULL,
            detail       TEXT
        );
        """
    )
    conn.commit()
    return conn

def upsert_torrent(conn: sqlite3.Connection, item: Dict[str, Any]) -> None:
    ts = now_iso()
    conn.execute(
        """
        INSERT INTO torrents (
            info_hash, title, category, torrent_url, magnet,
            published_at, published_raw, size_bytes, size_text,
            seeders, leechers, uploader, first_seen, last_seen
        ) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?)
        ON CONFLICT(info_hash) DO UPDATE SET
            title=excluded.title,
            category=excluded.category,
            torrent_url=excluded.torrent_url,
            magnet=excluded.magnet,
            published_at=excluded.published_at,
            published_raw=excluded.published_raw,
            size_bytes=excluded.size_bytes,
            size_text=excluded.size_text,
            seeders=excluded.seeders,
            leechers=excluded.leechers,
            uploader=excluded.uploader,
            last_seen=excluded.last_seen
        """,
        (
            item["info_hash"],
            item["title"],
            item["category"],
            item["torrent_url"],
            item["magnet"],
            item["published_at"],
            item["published_raw"],
            item["size_bytes"],
            item["size_text"],
            item["seeders"],
            item["leechers"],
            item["uploader"],
            ts,
            ts,
        ),
    )

def get_torrent_by_hash(conn: sqlite3.Connection, info_hash: str) -> Optional[sqlite3.Row]:
    return conn.execute("SELECT info_hash,title,magnet FROM torrents WHERE info_hash = ?", (info_hash,)).fetchone()

def record_push(
    conn: sqlite3.Connection, info_hash: str, title: str, ok: bool, detail: str
) -> None:
    ts = now_iso()
    conn.execute(
        """
        UPDATE torrents
           SET push_status=?, push_attempts=push_attempts+1, last_push_at=?, push_error=?
         WHERE info_hash=?
        """,
        ("success" if ok else "failed", ts, None if ok else detail[:1000], info_hash),
    )
    conn.execute(
        "INSERT INTO push_log(info_hash,title,attempted_at,success,detail) VALUES(?,?,?,?,?)",
        (info_hash, title, ts, 1 if ok else 0, detail[:2000]),
    )

# ---------------------------------------------------------------------------
# qBittorrent Web UI API 客户端
# ---------------------------------------------------------------------------
class QBitClient:
    def __init__(self, cfg: Dict[str, Any]):
        self.host = str(cfg.get("host", "127.0.0.1"))
        self.port = int(cfg.get("port", 8080))
        scheme = "https" if cfg.get("use_https") else "http"
        self.origin = f"{scheme}://{self.host}:{self.port}"
        self.base = self.origin + "/" + str(cfg.get("api_base", "api/v2")).strip("/")
        self.timeout = float(cfg.get("timeout_seconds", 15))
        self.username = str(cfg.get("username", "admin"))
        self.password = str(cfg.get("password", ""))
        self.auth_bypass = bool(cfg.get("auth_bypass", False))
        self.sid: Optional[str] = None
        self._logged_in = False
        self.session = requests.Session()
        self.session.headers.update(
            {
                "User-Agent": DEFAULT_USER_AGENT,
                "Referer": self.origin + "/",
            }
        )

    def login(self) -> None:
        if self.auth_bypass:
            self.session.cookies.clear()
            self.session.headers.pop("X-CSRF-Token", None)
            self._logged_in = True
            return
        resp = self.session.post(
            self.base + "/auth/login",
            data={"username": self.username, "password": self.password},
            timeout=self.timeout,
        )
        resp.raise_for_status()
        if "ok" not in resp.text.strip().lower():
            raise RuntimeError(f"登录失败，服务端返回：{resp.text[:200]!r}")
        sid = self.session.cookies.get("SID")
        if not sid:
            raise RuntimeError("登录成功但未获取到 SID cookie，请检查 Web UI 配置")
        self.sid = sid
        self.session.headers.update({"X-CSRF-Token": sid})
        self._logged_in = True

    def _ensure_login(self) -> None:
        if not self._logged_in:
            self.login()

    def _post_add(self, data: Dict[str, str]):
        if self.auth_bypass:
            return requests.post(
                self.base + "/torrents/add",
                data=data,
                headers=dict(self.session.headers),
                timeout=self.timeout,
            )
        return self.session.post(
            self.base + "/torrents/add", data=data, timeout=self.timeout
        )

    def add_magnet(self, magnet: str, qcfg: Dict[str, Any]) -> Tuple[bool, str]:
        data: Dict[str, str] = {"urls": magnet}
        if qcfg.get("category"):
            data["category"] = str(qcfg["category"])
        if qcfg.get("tags"):
            data["tags"] = ",".join(str(t) for t in qcfg["tags"])
        if qcfg.get("save_path"):
            data["savepath"] = str(qcfg["save_path"])
        if qcfg.get("paused"):
            data["paused"] = "true"
        for attempt in range(2):
            self._ensure_login()
            try:
                resp = self._post_add(data)
                if resp.status_code == 400 and "tags" in data:
                    LOG.debug("服务端拒绝 tags 参数，去掉后重试")
                    resp = self._post_add({k: v for k, v in data.items() if k != "tags"})
            except requests.RequestException as exc:
                raise RuntimeError(f"请求 qBittorrent 失败：{exc}") from exc
            if resp.status_code in (401, 403) and not self.auth_bypass:
                self.sid = None
                self._logged_in = False
                self.session.cookies.clear()
                continue
            if resp.status_code == 200:
                body = resp.text.strip()
                if body == "" or "ok" in body.lower():
                    return True, "已提交给 qBittorrent"
                raise RuntimeError(f"qBittorrent 返回：{body[:300]}")
            raise RuntimeError(f"HTTP {resp.status_code}：{resp.text[:300]}")
        raise RuntimeError("会话认证失效，重新登录后仍失败")

# ---------------------------------------------------------------------------
# GUI 窗口 PyQt6 QDialog
# ---------------------------------------------------------------------------
if HAVE_GUI:
    class ManualSelectWindow(QDialog):
        def __init__(self, hit_items, parent=None):
            super().__init__(parent)
            self.hit_items = hit_items
            self.user_selected_hashes: Set[str] = set()
            self.setWindowTitle("种子手动筛选 V2.0")
            self.resize(1200, 600)

            layout = QVBoxLayout(self)
            self.table = QTableWidget()
            cols = ["选择", "标题", "大小", "做种", "下载", "发布时间", "上传者", "info_hash"]
            self.table.setColumnCount(len(cols))
            self.table.setHorizontalHeaderLabels(cols)
            self.table.setRowCount(len(self.hit_items))

            for row_idx, item in enumerate(self.hit_items):
                cb = QCheckBox()
                cb.setChecked(False)
                self.table.setCellWidget(row_idx, 0, cb)

                self.table.setItem(row_idx,1, QTableWidgetItem(item.get("title","")))
                self.table.setItem(row_idx,2, QTableWidgetItem(item.get("size_text","")))
                self.table.setItem(row_idx,3, QTableWidgetItem(str(item.get("seeders","-"))))
                self.table.setItem(row_idx,4, QTableWidgetItem(str(item.get("leechers","-"))))
                self.table.setItem(row_idx,5, QTableWidgetItem(item.get("published_at","")))
                self.table.setItem(row_idx,6, QTableWidgetItem(item.get("uploader","")))

                hi = QTableWidgetItem(item.get("info_hash",""))
                hi.setToolTip(item.get("magnet",""))
                self.table.setItem(row_idx,7, hi)

            self.table.horizontalHeader().setSectionResizeMode(0, QHeaderView.ResizeMode.ResizeToContents)
            self.table.horizontalHeader().setSectionResizeMode(1, QHeaderView.ResizeMode.Stretch)
            for c in range(2,8):
                self.table.horizontalHeader().setSectionResizeMode(c, QHeaderView.ResizeMode.ResizeToContents)
            layout.addWidget(self.table)

            btn_layout = QVBoxLayout()
            self.btn_sel_all = QPushButton("全选")
            self.btn_unsel_all = QPushButton("取消全选")
            self.btn_confirm = QPushButton("确认勾选（返回主程序统一推送）")
            self.btn_skip = QPushButton("本组全部不选，跳过")

            self.btn_sel_all.clicked.connect(self._slot_sel_all)
            self.btn_unsel_all.clicked.connect(self._slot_unsel_all)
            self.btn_confirm.clicked.connect(self._slot_confirm)
            self.btn_skip.clicked.connect(self.reject)

            btn_layout.addWidget(self.btn_sel_all)
            btn_layout.addWidget(self.btn_unsel_all)
            btn_layout.addWidget(self.btn_confirm)
            btn_layout.addWidget(self.btn_skip)
            layout.addLayout(btn_layout)

        def _slot_sel_all(self):
            for r in range(self.table.rowCount()):
                self.table.cellWidget(r,0).setChecked(True)

        def _slot_unsel_all(self):
            for r in range(self.table.rowCount()):
                self.table.cellWidget(r,0).setChecked(False)

        def _slot_confirm(self):
            picked = set()
            for r in range(self.table.rowCount()):
                cb = self.table.cellWidget(r,0)
                if cb.isChecked():
                    picked.add(self.hit_items[r]["info_hash"])
            self.user_selected_hashes = picked
            self.accept()

# ---------------------------------------------------------------------------
# 核心业务：抓取解析入库，区分auto/manual
# ---------------------------------------------------------------------------
def run_core(cfg: Dict[str, Any], base_dir: Path, html_override: Optional[str]) -> Tuple[Set[str], sqlite3.Connection, List[List[Dict[str,Any]]]]:
    now = datetime.now()
    html_cache: Dict[str, str] = {}
    db_path = resolve_path(str(cfg["database"].get("path", "./torrents.db")), base_dir)
    conn = init_db(db_path)

    auto_hash_set: Set[str] = set()
    manual_item_groups: List[List[Dict[str,Any]]] = []

    total_terms = len(cfg["search-terms"])
    for idx, term in enumerate(cfg["search-terms"], start=1):
        label = str(term.get("name") or term["url"])
        run_mode = term.get("mode","auto")
        LOG.info(f"---搜索项 {idx}/{total_terms} name={label}, mode={run_mode} ---")

        if html_override is not None:
            html = html_override
        else:
            url = term["url"]
            if url in html_cache:
                html = html_cache[url]
            else:
                try:
                    html = fetch_html(url, cfg["global"])
                except Exception as exc:
                    LOG.error(f"抓取失败跳过：{exc}")
                    continue
                html_cache[url] = html

        items = parse_page(html, now)
        filters = term_filters(term)
        hit_list = []
        for it in items:
            ok, reason = passes_filters(it, filters, now)
            if ok:
                hit_list.append(it)
            else:
                LOG.debug(f"跳过《{it.get('title')}》: {reason}")
        LOG.info(f"解析{len(items)}条，命中 {len(hit_list)} 条")

        for hit in hit_list:
            upsert_torrent(conn, hit)
        conn.commit()

        if run_mode == "auto":
            for hit in hit_list:
                auto_hash_set.add(hit["info_hash"])
        elif run_mode == "manual":
            manual_item_groups.append(hit_list)

    LOG.info(f"auto模式命中待推送：{len(auto_hash_set)} 个hash；manual组数量：{len(manual_item_groups)}")
    return auto_hash_set, conn, manual_item_groups

def push_all_collected(conn: sqlite3.Connection, hash_set: Set[str], qbit_cfg: Dict[str, Any]):
    if not hash_set:
        LOG.info("没有收集到待推送种子，跳过qBittorrent推送")
        return
    if not qbit_cfg.get("enabled", False):
        LOG.info("qbittorrent推送在配置中关闭，跳过推送")
        return
    LOG.info(f"开始批量推送总共 {len(hash_set)} 个种子到qBittorrent")
    try:
        client = QBitClient(qbit_cfg)
        client.login()
    except Exception as e:
        LOG.error(f"qBittorrent登录失败：{e}")
        if qbit_cfg.get("record_failures", True):
            for h in hash_set:
                row = get_torrent_by_hash(conn, h)
                if row:
                    record_push(conn, row["info_hash"], row["title"], False, f"登录失败:{e}")
        conn.commit()
        return

    success = 0
    fail = 0
    for info_hash in hash_set:
        row = get_torrent_by_hash(conn, info_hash)
        if row is None:
            LOG.warning(f"数据库找不到hash {info_hash}，跳过")
            continue
        try:
            ok, detail = client.add_magnet(row["magnet"], qbit_cfg)
        except Exception as exc:
            ok, detail = False, str(exc)
        record_push(conn, row["info_hash"], row["title"], ok, detail)
        if ok:
            success +=1
        else:
            fail +=1
        LOG.info(f"【推送】《{row['title']}》 {'成功' if ok else '失败'}：{detail}")
    conn.commit()
    LOG.info(f"批量推送完成：成功={success}，失败={fail}")

# ---------------------------------------------------------------------------
# CLI / GUI入口
# ---------------------------------------------------------------------------
def main():
    parser = argparse.ArgumentParser(description=f"torrent_monitor V{SCRIPT_VERSION} 协议{REQUIRED_PROTOCOL_VERSION}")
    parser.add_argument("--config", default=str(Path(__file__).with_name("config.yaml")), help="yaml配置路径")
    parser.add_argument("--html-file", default=None, help="本地html调试解析")
    parser.add_argument("--dry-run", action="store_true", help="仅抓取入库，不推送qBittorrent")
    parser.add_argument("--gui", action="store_true", help="启用PyQt6图形界面（处理manual模式）")
    args = parser.parse_args()

    config_path = Path(args.config).expanduser().resolve()
    cfg = load_config(config_path)
    base_dir = config_path.parent
    setup_logging(cfg["logging"], base_dir)
    LOG.info("="*70)
    LOG.info(f"torrent_monitor V{SCRIPT_VERSION} 启动；协议版本 {REQUIRED_PROTOCOL_VERSION}")
    LOG.info(f"配置文件: {config_path}")

    local_html: Optional[str] = None
    if args.html_file:
        hp = Path(args.html_file).expanduser().resolve()
        local_html = hp.read_text(encoding="utf-8")
        LOG.info(f"调试模式，读取本地html：{hp}")

    auto_hash_set, conn, manual_groups = run_core(cfg, base_dir, local_html)

    manual_selected: Set[str] = set()
    if args.gui:
        if not HAVE_GUI:
            LOG.error("启用--gui但是没有安装PyQt6！请 pip install pyqt6")
        else:
            app = QApplication(sys.argv)
            for group_items in manual_groups:
                if len(group_items) == 0:
                    continue
                win = ManualSelectWindow(group_items)
                win.setWindowModality(Qt.WindowModality.ApplicationModal)
                win.exec()
                manual_selected.update(win.user_selected_hashes)
    else:
        for g in manual_groups:
            if len(g):
                names = [x["title"] for x in g]
                LOG.warning(f"CLI模式，跳过manual模式种子共{len(g)}条；开启--gui才可以人工选择。示例标题：{names[0][:60]}…")

    total_to_push: Set[str] = auto_hash_set.union(manual_selected)
    LOG.info(f"合并待推送集合：auto={len(auto_hash_set)}, manual-user-pick={len(manual_selected)} → 合计 {len(total_to_push)}")

    if not args.dry_run:
        push_all_collected(conn, total_to_push, cfg["qbittorrent"])
    else:
        LOG.info("[dry-run] 不执行qBittorrent推送，仅入库")

    stats = conn.execute("SELECT push_status, COUNT(*) n FROM torrents GROUP BY push_status").fetchall()
    LOG.info("数据库状态统计：%s", {r["push_status"]: r["n"] for r in stats})
    conn.close()
    LOG.info("运行结束。")

if __name__ == "__main__":
    sys.exit(main())
