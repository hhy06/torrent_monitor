#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
WSJ 种子监控 / qBittorrent 推送工具

流程：
  1. 读取 YAML 配置，抓取配置中的种子列表页（默认 TPB 用户页）。
  2. 解析每行种子：标题、分类、发布时间、大小、做种数、下载数、上传者、magnet。
  3. 按「标题包含关键字 + 大小上限 + 发布日期在最近 N 天」过滤。
  4. 把命中的种子全部字段写入 SQLite（可重复运行，按 info_hash 去重）。
  5. 把「新增的」或「之前推送失败」的 magnet 通过 qBittorrent Web UI API
     提交给局域网中的 qbittorrent-nox，并把推送结果写回数据库。
     后续下载、文件管理不在本脚本职责内。

用法：
  python torrent_monitor.py --config config.yaml
  python torrent_monitor.py --dry-run                 # 只抓取入库，不推送
  python torrent_monitor.py --html-file sample.html   # 用本地 HTML 调试解析

依赖：pip install requests beautifulsoup4 PyYAML
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
from typing import Any, Dict, List, Optional, Tuple

import requests
import yaml
from bs4 import BeautifulSoup

LOG = logging.getLogger("torrent_monitor")

DEFAULT_USER_AGENT = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/124.0 Safari/537.36"
)

# TPB 服务器时间与本机可能有微小差异，允许 12 小时的"未来"容差
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
    """当前本地时间，ISO 格式（秒级）。"""
    return datetime.now().replace(microsecond=0).isoformat()


def resolve_path(value: str, base_dir: Path) -> Path:
    """相对路径按配置文件所在目录解析。"""
    p = Path(value).expanduser()
    return p if p.is_absolute() else (base_dir / p).resolve()


def load_config(path: Path) -> Dict[str, Any]:
    with path.open("r", encoding="utf-8") as f:
        cfg = yaml.safe_load(f) or {}
    if not isinstance(cfg, dict):
        raise ValueError("配置文件顶层必须是映射（key: value）结构")
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
    return cfg


def term_filters(term: Dict[str, Any]) -> Dict[str, Any]:
    """把单个 search-term 归一化成 passes_filters 使用的 filters。"""
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
    """把 '34.03 MiB' / '1.74 GiB' 之类的文本换算成字节数。"""
    m = SIZE_RE.search(text.replace("\xa0", " ").strip())
    if not m:
        return None
    num_str = m.group(1)
    # 兼容 '1,234.56'（千分位逗号）和 '34,03'（欧洲小数点逗号）
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
    """解析 TPB 的三种日期写法：Today HH:MM / Y-day HH:MM / MM-DD HH:MM。"""
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
        # 跨年的情况：若算出来的时间明显在未来，则回退一年
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
    """优先使用 btih；没有 btih 时用 magnet 本身的 sha1 作为稳定主键。"""
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
        except Exception as exc:  # noqa: BLE001 - 网络层异常类型较多，统一处理
            last_error = exc
            LOG.warning("抓取失败：%s", exc)
            if attempt < retries:
                time.sleep(1.5 * (attempt + 1))

    raise RuntimeError(f"抓取页面失败（已重试 {retries} 次）：{last_error}")


def parse_page(html: str, now: datetime) -> List[Dict[str, Any]]:
    """从 TPB 列表页的 <tr> 中提取种子信息。"""
    soup = BeautifulSoup(html, "html.parser")
    results: List[Dict[str, Any]] = []

    for tr in soup.find_all("tr"):
        links = [a for a in tr.find_all("a", href=True)]

        # 标题链接：href 含 /torrent/ 且 title 为 "Details for ..."
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

        # 分类
        category = None
        cat_a = next((a for a in links if "/browse/" in a["href"]), None)
        if cat_a:
            category = cat_a.get_text(" ", strip=True) or None

        # 上传者：/user/ 链接中有文字的那个（排除只有 icon 的 VIP 链接）
        uploader = None
        for a in links:
            if "/user/" in a["href"] and a.get_text(strip=True):
                uploader = a.get_text(strip=True)
                break

        # 日期：找到第一个能被识别为 TPB 日期的 td
        published_raw, published_dt = None, None
        for td in tds:
            txt = td.get_text(" ", strip=True).replace("\xa0", " ")
            parsed = parse_tpb_date(txt, now)
            if parsed is not None:
                published_raw, published_dt = txt, parsed
                break

        # 大小：含 KiB/MiB/GiB 等单位的 td
        size_text, size_bytes = None, None
        for td in tds:
            txt = td.get_text(" ", strip=True).replace("\xa0", " ")
            m = SIZE_RE.search(txt)
            if m:
                size_text = txt
                size_bytes = parse_size(txt)
                break

        # 做种数 / 下载数：大小列之后的两个纯数字 td
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
    """返回 (是否命中, 未命中原因)。"""
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
        limit = float(max_mb) * 1024 * 1024  # MiB -> 字节
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
    """新记录插入；已存在则更新种子自身信息，但保留推送状态。"""
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


def get_pending_push(conn: sqlite3.Connection) -> List[sqlite3.Row]:
    """新增（pending）以及之前推送失败（failed）的种子。"""
    return conn.execute(
        "SELECT info_hash, title, magnet FROM torrents "
        "WHERE push_status IN ('pending','failed') ORDER BY published_at DESC, first_seen DESC"
    ).fetchall()


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
    """通过 qBittorrent Web UI (API v2) 提交 magnet。"""

    def __init__(self, cfg: Dict[str, Any]):
        self.host = str(cfg.get("host", "127.0.0.1"))
        self.port = int(cfg.get("port", 8080))
        scheme = "https" if cfg.get("use_https") else "http"
        self.origin = f"{scheme}://{self.host}:{self.port}"
        self.base = self.origin + "/" + str(cfg.get("api_base", "api/v2")).strip("/")
        self.timeout = float(cfg.get("timeout_seconds", 15))
        self.username = str(cfg.get("username", "admin"))
        self.password = str(cfg.get("password", ""))
        # Web UI 对白名单 IP 免密时，不需要走 auth/login
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
            # 免密模式不需要登录。注意：服务端每次响应都会下发一个 SID，
            # 但带上这个 SID 再请求反而会被判为无效会话（404），
            # 所以这里清空 cookie，且在每次 add 前也会清空。
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
        # qBittorrent 4.3+ 的 CSRF 防护：需要把 SID 放进请求头
        self.session.headers.update({"X-CSRF-Token": sid})
        self._logged_in = True

    def _ensure_login(self) -> None:
        if not self._logged_in:
            self.login()

    def _post_add(self, data: Dict[str, str]):
        if self.auth_bypass:
            # 实测该 Web UI（v4.1.5 免密）在同一个 Session 上连续 POST 会返回 404，
            # 每次新建会话则正常，所以这里不复用长连接会话。
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
                    # qBittorrent 4.1.x 尚不支持 tags 参数，去掉后重试
                    LOG.debug("服务端拒绝 tags 参数，去掉后重试")
                    resp = self._post_add({k: v for k, v in data.items() if k != "tags"})
            except requests.RequestException as exc:
                raise RuntimeError(f"请求 qBittorrent 失败：{exc}") from exc

            if resp.status_code in (401, 403) and not self.auth_bypass:
                # 会话过期（仅密码登录模式）：清掉重新登录再试一次
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
# 主流程
# ---------------------------------------------------------------------------
def parse_args(argv: Optional[List[str]] = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="种子抓取 / SQLite 入库 / qBittorrent 推送")
    parser.add_argument(
        "--config",
        default=str(Path(__file__).with_name("config.yaml")),
        help="YAML 配置文件路径（默认：脚本同目录的 config.yaml）",
    )
    parser.add_argument("--html-file", default=None, help="从本地 HTML 文件读取（调试解析用）")
    parser.add_argument("--dry-run", action="store_true", help="只抓取入库，不向 qBittorrent 推送")
    return parser.parse_args(argv)


def main(argv: Optional[List[str]] = None) -> int:
    args = parse_args(argv)
    config_path = Path(args.config).expanduser().resolve()
    cfg = load_config(config_path)
    base_dir = config_path.parent
    setup_logging(cfg["logging"], base_dir)

    LOG.info("=" * 64)
    LOG.info("开始运行，配置文件：%s", config_path)

    # 1~3) 逐个搜索项：抓取 -> 解析 -> 过滤
    now = datetime.now()
    html_cache: Dict[str, str] = {}
    local_html: Optional[str] = None
    if args.html_file:
        html_path = Path(args.html_file).expanduser().resolve()
        LOG.info("从本地 HTML 文件读取：%s（将用于全部搜索项）", html_path)
        local_html = html_path.read_text(encoding="utf-8")

    matched: List[Dict[str, Any]] = []
    total_terms = len(cfg["search-terms"])
    for idx, term in enumerate(cfg["search-terms"], start=1):
        label = str(term.get("name") or term["url"])
        LOG.info("--- 搜索项 %d/%d：%s ---", idx, total_terms, label)

        if local_html is not None:
            html = local_html
        else:
            url = str(term["url"])
            if url in html_cache:
                LOG.info("复用已抓取的页面：%s", url)
                html = html_cache[url]
            else:
                try:
                    html = fetch_html(url, cfg["global"])
                except Exception as exc:  # noqa: BLE001
                    LOG.error("抓取失败，跳过该搜索项：%s", exc)
                    continue
                html_cache[url] = html

        LOG.info("HTML 长度：%d 字符", len(html))
        items = parse_page(html, now)
        term_matched: List[Dict[str, Any]] = []
        for item in items:
            ok, reason = passes_filters(item, term_filters(term), now)
            if ok:
                term_matched.append(item)
            else:
                LOG.debug("跳过《%s》：%s", item["title"], reason)
        LOG.info("解析 %d 条，命中 %d 条", len(items), len(term_matched))
        matched.extend(term_matched)

    LOG.info("全部搜索项共命中：%d 条", len(matched))

    # 4) 入库
    db_path = resolve_path(str(cfg["database"].get("path", "./torrents.db")), base_dir)
    conn = init_db(db_path)
    for item in matched:
        upsert_torrent(conn, item)
    conn.commit()
    LOG.info("数据库已更新：%s", db_path)

    # 5) 推送
    qcfg = cfg["qbittorrent"]
    if args.dry_run:
        LOG.info("[dry-run] 跳过 qBittorrent 推送")
    elif not qcfg.get("enabled", False):
        LOG.info("qBittorrent 推送已在配置中禁用")
    else:
        pending = get_pending_push(conn)
        LOG.info("待推送（新增或此前失败）：%d 条", len(pending))
        if pending:
            client = QBitClient(qcfg)
            logged_in = False
            try:
                client.login()
                logged_in = True
                LOG.info("已登录 qBittorrent Web UI：%s", client.base)
            except Exception as exc:  # noqa: BLE001
                LOG.error("登录 qBittorrent 失败：%s", exc)
                if qcfg.get("record_failures", True):
                    for row in pending:
                        record_push(conn, row["info_hash"], row["title"], False, f"登录失败：{exc}")

            if logged_in:
                for row in pending:
                    try:
                        ok, detail = client.add_magnet(row["magnet"], qcfg)
                    except Exception as exc:  # noqa: BLE001
                        ok, detail = False, str(exc)
                    record_push(conn, row["info_hash"], row["title"], ok, detail)
                    LOG.info("《%s》推送%s：%s", row["title"], "成功" if ok else "失败", detail)
        conn.commit()

    # 6) 汇总
    stats = conn.execute(
        "SELECT push_status, COUNT(*) AS n FROM torrents GROUP BY push_status"
    ).fetchall()
    LOG.info("数据库推送状态统计：%s", {r["push_status"]: r["n"] for r in stats})
    conn.close()
    LOG.info("运行结束")
    return 0


if __name__ == "__main__":
    sys.exit(main())
