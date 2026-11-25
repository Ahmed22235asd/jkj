import base64, hashlib, hmac, json, os, queue, re, secrets, shutil, subprocess, sys, threading, time, webbrowser
from concurrent.futures import ThreadPoolExecutor
from http.cookies import SimpleCookie
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import parse_qs, parse_qsl, unquote, urlencode, urljoin, urlparse, urlunparse

import requests

HERE = os.path.dirname(os.path.abspath(__file__))
TL = threading.local()          # per-thread: .job (studio job: log + cancel flag), .entry (the episode row being worked on), .pool (download pool)
LOCK = threading.Lock()
UA = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/130.0.0.0 Safari/537.36"


def opt(name, default, cast=str):
    for a in sys.argv:
        if a.startswith(f"--{name}="):
            try:
                return cast(a.split("=", 1)[1])
            except ValueError:
                pass
    return default


MAXWAIT = opt("wait", 75.0, float)
IDLE = opt("idle", 12.0, float)
MIN_MIN = opt("min-minutes", 10.0, float)
WORKERS = opt("workers", 16, int)
OUT = opt("out", "downloads")
QUALITY = opt("quality", "best")
ONLY = [x for x in opt("only", "").lower().split(",") if x]
NO_LULU = "--no-lulu" in sys.argv
NO_OUTER = "--no-outer" in sys.argv
GRAB_ONLY = "--grab-only" in sys.argv
HEADLESS = "--headless" in sys.argv
EP_FROM, EP_TO = opt("from", None, float), opt("to", None, float)
SEASONS = [int(x) for x in opt("seasons", "").split(",") if x.strip().isdigit()]
MEGA_REFERER = "https://eg.megamax.cam/"
AZ_REFERER = "https://animezid.org/"

# ---- host preference ----
ALIASES = {"streamhg": ("streamhg", "streamwish", "hgcloud"), "byse": ("byse",), "uqload": ("uqload",)}
PREFERRED = [("streamhg", "streamwish", "hgcloud"), ("byse",), ("uqload",)]
AVOID = []
USE_CHROMIUM = "--chromium" in sys.argv
OTHERS = ["earnvids", "filelions", "vidhide", "mp4upload", "krakenfiles", "voe", "filemoon", "streamtape", "doodstream", "dood", "mixdrop"]
LULU = ("lulustream", "lulu", "luluvid")

# ---- ad blocking ----
AD_DOMAINS = ("ser-46-host.store", "agl006.host", "asiafilm.org", "directyp.org", "xbeat.space", "nresystems.com", "predictivadnetwork.com",
              "histats.com", "googlesyndication.com", "googletagmanager.com", "google-analytics.com", "doubleclick.net", "adsterra", "popads",
              "monetag", "propellerads", "exoclick", "juicyads", "popcash", "clickadu", "hilltopads", "adcash", "trafficjunky", "onclick",
              "bidgear", "richads", "pushnami", "a-ads.com", "admaven", "yllix", "tsyndicate", "profitableratecpm", "effectivegatecpm",
              "cpmstar", "adskeeper", "mgid.com", "traffmovie", "burnetsasgmt", "clarity.ms", "cloudflareinsights.com", "adangle",
              "1xbet", "betwinner", "melbet", "linebet", "mostbet", "creative-cdn", "adexchangeclear", "adnxs", "criteo", "taboola", "outbrain")
AD_PATH = ("/content/stream/agl/", "/vast", "/ads/", "adserve", "popunder", "/banner")
NOT_VIDEO = ("preview", "thumb", "sprite", "trailer", "/ads/", "banner", "1xbet", "/content/stream/agl/")
MEDIA_RX = re.compile(r"\.(m3u8|mp4)(\?|#|$)|/master\.txt|urlset/master|/hls\d*/[^?]*\.txt", re.I)
ADBLOCK = [True]          # the AnimeZid page itself is retried once WITHOUT blocking if blocking leaves it without a player

INIT_JS = """(() => {
  try { window.open = () => ({closed:false, focus(){}, blur(){}, close(){}, postMessage(){}, document:{write(){},close(){}}, location:{href:''}}); } catch(e){}
  try { Object.defineProperty(navigator,'webdriver',{get:()=>undefined}); } catch(e){}
  document.addEventListener('click', e => { const a = e.target && e.target.closest && e.target.closest('a[target=_blank]'); if (a) e.preventDefault(); }, true);
})();"""
JS_PLAY = """() => {
  try { document.querySelectorAll('video').forEach(v => { v.muted = true; const p = v.play(); if (p && p.catch) p.catch(()=>{}); }); } catch(e){}
  try { document.querySelectorAll('.jw-icon-display,.jw-display-icon-container,.vjs-big-play-button,.plyr__control--overlaid,#play,[class*="play-btn"],[class*="play_btn"],[aria-label="Play"],.fp-play,.play-button').forEach(b => b.click()); } catch(e){}
  try { if (window.jwplayer) jwplayer().play(); } catch(e){}
}"""
JS_PAUSE = "() => { document.querySelectorAll('video').forEach(v => { try { v.muted = true; v.pause(); } catch (e) {} }); }"
JS_VSTATE = """() => { let loading=false, playing=false, has=false;
  document.querySelectorAll('video').forEach(v => { has=true; if (!v.paused && v.readyState>=2) playing=true;
    if (!v.ended && (v.networkState===2 || (v.readyState<3 && (v.currentSrc||v.src)))) loading=true; });
  return {has, playing, loading}; }"""
JS_INERTIA = """async (u) => {
  const ck = decodeURIComponent((document.cookie.match(/XSRF-TOKEN=([^;]+)/) || [])[1] || '');
  const pg = JSON.parse(document.querySelector('script[data-page]').textContent);
  const r = await fetch(u, {headers: {'Accept': 'text/html, application/xhtml+xml', 'X-Inertia': 'true', 'X-Inertia-Version': pg.version,
     'X-Inertia-Partial-Component': pg.component, 'X-Inertia-Partial-Data': 'streams', 'X-Inertia-Except-Once-Props': 'video,config,ads',
     'X-Requested-With': 'XMLHttpRequest', 'X-XSRF-TOKEN': ck}, credentials: 'include'});
  return {status: r.status, text: await r.text(), name: (pg.props && pg.props.video && pg.props.video.name) || ''};
}"""
# server buttons of the AnimeZid watch page (same finder the old project used)
SERVER_RX = (r"megamax|vidtube|yourupload|videa|sendvid|streamlare|mega\b|sibnet|vidmoly|4meplayer|michi|google|\bok\b|kraken|streamhg|turbovid|vidhls|leech|earnvids|streamruby|"
             r"mixdrop|dood|uqload|voe|filemoon|streamwish|vidhide|lulustream|streamtape|mp4upload|okru|ok\.ru|vidoza|upstream|hgcloud|vkvideo")
JS_SERVERS = r"""(a) => {
  const re = new RegExp(a.rx, 'i'), bad = /جارٍ|loading|اختر|السيرفر الحالي|select|choose|تحميل|download|share|مشاركة|إبلاغ|report|login|تسجيل/i;
  const qual = /^[\w.\-]+\s+(?:FHD|HD|SD|4K|1080p?|720p?|480p?|360p?)$/i;
  document.querySelectorAll('[data-hx]').forEach(e => { delete e.dataset.hx; });
  const n = s => (s || '').trim().replace(/\s+/g, ' ');
  const first = el => n((el.innerText || '').split('\n')[0]);
  const dl = [...document.querySelectorAll('h1,h2,h3,h4,h5')].find(h => /سيرفرات التحميل|روابط التحميل/.test(h.textContent || ''));
  const clickable = el => !!el.closest('li, a, button, [role="tab"], [onclick], [tabindex]') || getComputedStyle(el).cursor === 'pointer';
  const rows = new Map();
  const add = (el, name) => {
    const row = el.closest('li, a, button, [role="tab"]') || el, r = row.getBoundingClientRect();
    if (!name || name.length > 30 || bad.test(name) || row.closest('nav, header, footer') || !(r.width > 0 && r.height > 0)) return;
    if (dl && (dl.compareDocumentPosition(row) & Node.DOCUMENT_POSITION_FOLLOWING)) return;
    const key = name.toLowerCase(), c = clickable(el), old = rows.get(key);
    if (!old || (c && !old.c)) rows.set(key, {row, name, c});
  };
  document.querySelectorAll('[data-server],[data-embed],[class*="server" i] li,[class*="server" i] a,[class*="server" i] button,[id*="server" i] li,[id*="server" i] a,[id*="server" i] button')
    .forEach(el => add(el, first(el) || n(el.getAttribute('data-name') || el.title)));
  document.querySelectorAll('body *').forEach(el => {
    const t = first(el);
    if (!t || t.length > 30 || [...el.children].some(c => first(c) === t)) return;
    if ((re.test(t) && t.length <= 25) || qual.test(t)) add(el, t);
  });
  return [...rows.values()].map((r, i) => { r.row.dataset.hx = String(i); return {idx: i, name: r.name}; });
}"""
JS_IFRAMES = r"""() => [...document.querySelectorAll('iframe')].map(f => f.src || f.getAttribute('data-src') || '').filter(Boolean)"""
JS_ANCHORS = r"""() => [...document.querySelectorAll('a[href]')].map(a => ({href: a.href, text: (a.innerText || '').replace(/\s+/g, ' ').trim(), title: (a.title || '').trim()}))"""

# in-player HLS downloader (from the old project): runs INSIDE the player frame, same origin / TLS / cookies as the video itself
JS_HLS_DL = r"""
async (cfg) => {
  const P = window.__mmp = {state: "start", done: 0, total: 0, bytes: 0, err: null, limit: cfg.conc, fails: 0, dur: 0};
  const sleep = (ms) => new Promise(r => setTimeout(r, ms));
  try {
    const abs = (u, b) => new URL(u, b).href;
    const getText = async (u) => { const r = await fetch(u); if (!r.ok) throw new Error("HTTP " + r.status + " " + u.slice(0, 100)); return r.text(); };
    const getBuf = async (u) => { const r = await fetch(u); if (!r.ok) throw new Error("HTTP " + r.status + " " + u.slice(0, 100)); return r.arrayBuffer(); };
    const retry = async (fn) => { let last; for (let t = 0; t < cfg.retries; t++) { try { return await fn(); } catch (e) { last = e; await sleep(Math.min(cfg.backoff * 1000 * 2 ** t, 6000)); } } throw last; };
    let base = cfg.url, text = await retry(() => getText(base));
    if (text.includes("#EXT-X-STREAM-INF")) {
      const L = text.split(/\r?\n/); let best = null, bw = -1;
      for (let i = 0; i < L.length; i++) if (L[i].startsWith("#EXT-X-STREAM-INF")) {
        const m = /BANDWIDTH=(\d+)/.exec(L[i]); const b = m ? +m[1] : 0;
        let j = i + 1; while (j < L.length && (L[j].trim() === "" || L[j].startsWith("#"))) j++;
        if (j < L.length && b > bw) { bw = b; best = L[j].trim(); }
      }
      if (!best) throw new Error("no variant in master playlist");
      base = abs(best, base); text = await retry(() => getText(base));
    }
    P.dur = [...text.matchAll(/#EXTINF:([\d.]+)/g)].reduce((a, m) => a + +m[1], 0);
    let key = null, map = null, seq = 0; const segs = [];
    for (const raw of text.split(/\r?\n/)) {
      const s = raw.trim();
      if (s.startsWith("#EXT-X-MEDIA-SEQUENCE:")) seq = parseInt(s.split(":")[1]) || 0;
      else if (s.startsWith("#EXT-X-KEY:")) {
        const meth = /METHOD=([^,]+)/.exec(s)[1];
        if (meth === "NONE") key = null;
        else if (meth !== "AES-128") throw new Error("unsupported encryption " + meth);
        else { const u = /URI="([^"]+)"/.exec(s)[1], iv = /IV=0x([0-9a-fA-F]+)/.exec(s); key = {uri: abs(u, base), iv: iv ? iv[1] : null}; }
      } else if (s.startsWith("#EXT-X-MAP:")) map = abs(/URI="([^"]+)"/.exec(s)[1], base);
      else if (s && !s.startsWith("#")) segs.push({u: abs(s, base), key, seq: seq++});
    }
    if (!segs.length) throw new Error("empty media playlist");
    P.ready = true;
    if (cfg.minsec && P.dur < cfg.minsec) throw new Error("too short: " + Math.round(P.dur / 60) + " min");
    const jobs = []; if (map) jobs.push([-1, map, null, 0]);
    segs.forEach((s, i) => jobs.push([i, s.u, s.key, s.seq]));
    P.total = jobs.length;
    const have = new Set(cfg.have || []);
    const todo = jobs.filter(j => !have.has(j[0])); P.done = jobs.length - todo.length;
    const keys = {};
    const getKey = async (k) => keys[k.uri] || (keys[k.uri] = crypto.subtle.importKey("raw", await getBuf(k.uri), "AES-CBC", false, ["decrypt"]));
    const ivOf = (k, n) => { if (k.iv) { const h = k.iv.padStart(32, "0"); return Uint8Array.from(h.match(/../g).map(x => parseInt(x, 16))); }
      const a = new Uint8Array(16); new DataView(a.buffer).setUint32(12, n); return a; };
    const b64 = (buf) => new Promise(res => { const f = new FileReader(); f.onload = () => res(f.result.split(",")[1]); f.readAsDataURL(new Blob([buf])); });
    let streak = 0;
    const work = async (idx, u, k, n) => {
      let last = null;
      for (let t = 0; t < cfg.retries; t++) {
        try {
          let buf = await getBuf(u);
          if (k) buf = await crypto.subtle.decrypt({name: "AES-CBC", iv: ivOf(k, n)}, await getKey(k), buf);
          if (!(await window.__mmsave(idx, await b64(buf)))) throw new Error("save failed");
          P.bytes += buf.byteLength; P.done++;
          if (++streak >= 15 && P.limit < cfg.conc) { P.limit++; streak = 0; }
          return;
        } catch (e) { last = e; P.fails++; streak = 0; P.limit = Math.max(1, P.limit - 1); await sleep(Math.min(cfg.backoff * 1000 * 2 ** t, 6000)); }
      }
      throw last;
    };
    let next = 0;
    await Promise.all(Array.from({length: cfg.conc}, async (_, w) => {
      while (next < todo.length && !P.err) {
        if (w >= P.limit) { await sleep(300); continue; }
        const j = todo[next++];
        try { await work(...j); } catch (e) { P.err = String((e && e.message) || e); }
      }
    }));
    if (P.err) throw new Error(P.err);
    P.state = "done";
  } catch (e) { P.err = String((e && e.message) || e); P.state = "error"; }
}
"""


def log(*a):
    print(*a, flush=True)


def cancelled():
    j = getattr(TL, "job", None)
    return bool(j and j.get("cancel"))


def set_entry(**kw):
    e = getattr(TL, "entry", None)
    if e is not None:
        with LOCK:
            e.update(kw)


# --- the player may refuse to SHOW the video (anti-adblock wall) and still produce / contain the m3u8: look in the page too ---
PACKED_RE = re.compile(r"}\('(.*)',(\d+),(\d+),'(.*?)'\.split\('\|'\)", re.S)
MEDIA_TEXT_RE = re.compile(r'https?:?(?:\\?/){2}(?:[^\s"\'<>\\]|\\/)+?\.(?:m3u8|mp4)(?:[^\s"\'<>\\]|\\/)*', re.I)   # also JS-escaped urls (https:\/\/host\/a.m3u8)
WALL_RX = re.compile(r"turn off .{0,20}ad ?block|disable .{0,20}ad ?block|ad ?block.{0,30}(detected|enabled)|أوقف.{0,15}(مانع|حاجب)|عطل.{0,15}(مانع|حاجب)", re.I)
JS_SCAN = """() => {
  const out = [];
  try { performance.getEntriesByType('resource').forEach(e => out.push(e.name)); } catch (e) {}
  try { document.querySelectorAll('video,source').forEach(v => { if (v.currentSrc) out.push(v.currentSrc); if (v.src) out.push(v.src); }); } catch (e) {}
  try { if (window.jwplayer) { const p = jwplayer().getPlaylist() || []; p.forEach(i => { (i.sources || []).forEach(s => out.push(s.file)); if (i.file) out.push(i.file); }); } } catch (e) {}
  try { if (window.videojs) Object.values(videojs.getPlayers()).forEach(p => { if (p && p.currentSrc) out.push(p.currentSrc()); }); } catch (e) {}
  return out.filter(x => typeof x === 'string' && x);
}"""
JS_WALL = "() => (document.body && document.body.innerText || '').slice(0, 600)"


def _base(n, base):
    d = "0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"
    return d[n] if n < base else _base(n // base, base) + d[n % base]


def unpack(text):
    out = []
    for m in PACKED_RE.finditer(text):
        payload, a, c, words = m.group(1), int(m.group(2)), int(m.group(3)), m.group(4).split("|")
        table = {}
        for i in range(c):
            table[_base(i, a)] = words[i] if i < len(words) and words[i] else _base(i, a)
        out.append(re.sub(r"\b\w+\b", lambda x: table.get(x.group(0), x.group(0)), payload.replace("\\'", "'")))
    return "\n".join(out)


def find_in_text(text, page_url):
    import html as _h
    text = text + "\n" + unpack(text)
    found = []
    for m in MEDIA_TEXT_RE.finditer(text):
        u = _h.unescape(m.group(0).replace("\\/", "/")).rstrip("\\")
        u = "https:" + u if u.startswith("//") else u
        if u not in found:
            found.append(u)
    for m in re.finditer(r'["\'](/[^"\'\s]+\.(?:m3u8|mp4)[^"\'\s]*)["\']', text):
        u = urljoin(page_url, m.group(1))
        if u not in found:
            found.append(u)
    return found


def safe_name(s):
    return re.sub(r"[^\w\-.]+", "_", s, flags=re.UNICODE).strip("_.") or "video"


def is_ad(url):
    u = url.lower()
    host = urlparse(u).hostname or ""
    return any(d in host for d in AD_DOMAINS) or any(p in u for p in AD_PATH)


def is_media(url):
    if not url or url.startswith(("blob:", "data:")) or is_ad(url):
        return False
    u = url.lower()
    return bool(MEDIA_RX.search(u)) and not any(w in u for w in NOT_VIDEO)


def rank(u):
    p = u.lower().split("?")[0]
    if p.endswith(".m3u8"):
        return 0 if "master" in p else 1
    return 3 if p.endswith(".mp4") else 2


# ================================================================= ordering (pure logic)
def set_preferred(csv):
    global PREFERRED
    names = [x.strip().lower() for x in str(csv or "").split(",") if x.strip()]
    PREFERRED = [ALIASES.get(n, (n,)) for n in names]


def height_of(q):
    m = re.search(r"(\d{3,4})x(\d{3,4})", q.get("resolution") or "")
    if m:
        return int(m.group(2))
    m = re.search(r"(\d{3,4})p", q.get("label") or "")
    return int(m.group(1)) if m else 0


def host_tier(driver):
    """MegaMax inner host -> (group, index) | None.   0 preferred, 1 lulustream, 2 others"""
    d = (driver or "").lower()
    if ONLY and not any(o in d for o in ONLY):
        return None
    if any(a in d for a in AVOID):
        return None
    for i, keys in enumerate(PREFERRED):
        if any(k in d for k in keys):
            return (0, i)
    if any(k in d for k in LULU):
        return None if NO_LULU else (1, 0)
    for i, k in enumerate(OTHERS):
        if k in d:
            return (2, i)
    return (2, 99)


def build_candidates(streams):
    maxh = int(QUALITY) if str(QUALITY).isdigit() else 99999
    out, seen = [], set()
    for q in streams.get("data", []):
        h = height_of(q)
        if h and h > maxh:
            continue
        for m in q.get("mirrors", []):
            t = host_tier(m.get("driver"))
            link = m.get("link") or ""
            if t is None or not link or link in seen:
                continue
            seen.add(link)
            out.append({"type": "mega", "group": t[0], "hidx": t[1], "height": h, "label": q.get("label"), "driver": m["driver"],
                        "embed": "https:" + link if link.startswith("//") else link, "method": "browser" if t[0] == 1 else "python"})
    out.sort(key=lambda c: (c["group"], -c["height"], c["hidx"]))
    return out


def build_plan(mega, outer_names):
    """mega: build_candidates() result;  outer_names: AnimeZid page server names (MegaMax already removed)"""
    outer = []
    for i, n in enumerate(outer_names):
        if (ONLY and not any(o in n.lower() for o in ONLY)) or any(a in n.lower() for a in AVOID):
            continue
        outer.append({"type": "outer", "driver": n, "label": "page", "height": 0, "method": "python", "embed": None,
                      "pref": "uqload" in n.lower(), "i": i})
    return ([c for c in mega if c["group"] == 0] + [o for o in outer if o["pref"]] + [c for c in mega if c["group"] == 1]
            + [c for c in mega if c["group"] == 2] + [o for o in outer if not o["pref"]])


# ================================================================= browser plumbing
def route(r):
    try:
        rq = r.request
        if is_ad(rq.url):
            try:
                if rq.is_navigation_request() and rq.frame.parent_frame is None:
                    return r.fulfill(status=204, body="")      # an ad tried to take over the tab
            except Exception:
                pass
            if ADBLOCK[0]:
                return r.abort()
        r.continue_()
    except Exception:
        pass


def _close_popup(pg):
    try:
        if pg.opener() is not None:
            pg.close()
    except Exception:
        pass


JOBS = {}      # page -> download job (the player frame hands segments to python through __mmsave)


def _save_binding(source, idx, b64):
    try:
        job = JOBS.get(source["page"])
        if not job:
            return False
        data = base64.b64decode(b64)
        with open(os.path.join(job["dir"], f"{int(idx) + 1:07d}.part"), "wb") as f:
            f.write(data)
        job["bytes"] += len(data)
        return True
    except Exception:
        return False


PW = [None]
RELAXED = [None]


def new_context(p, relaxed=False):
    """-> (closer, ctx).  Real Chrome (falls back to Playwright's Chromium), persistent profile so Cloudflare / site cookies survive restarts.
    Web security is relaxed on purpose: the in-player downloader must read cross-origin segments and real HTTP codes (FetchV style)."""
    global UA
    PW[0] = p
    profile = os.path.join(HERE, "mmgrab_profile_lulu" if relaxed else "mmgrab_profile")
    flags = ["--disable-blink-features=AutomationControlled", "--autoplay-policy=no-user-gesture-required"]
    if relaxed:     # only the lulustream in-player downloader needs this; AnimeZid's own "session check" breaks with it
        flags += ["--disable-web-security", "--disable-site-isolation-trials"]
    kw = dict(headless=HEADLESS, args=flags,
              ignore_default_args=["--enable-automation"], viewport={"width": 1280, "height": 720})
    ctx = None
    if not USE_CHROMIUM:
        try:
            ctx = p.chromium.launch_persistent_context(profile, channel="chrome", **kw)
        except Exception as e:
            log("   (Google Chrome could not be started:", (str(e).splitlines() or ["?"])[0][:90], "-> using Playwright's Chromium)")
    if ctx is None:
        ctx = p.chromium.launch_persistent_context(profile, **kw)
    ctx.add_init_script(INIT_JS)
    ctx.route("**/*", route)
    ctx.on("page", _close_popup)
    ctx.expose_binding("__mmsave", _save_binding)
    pg = ctx.pages[0] if ctx.pages else ctx.new_page()
    try:
        UA = (pg.evaluate("navigator.userAgent") or UA).replace("HeadlessChrome", "Chrome")   # same identity for python checks and downloads
    except Exception:
        pass
    return ctx, ctx


def relaxed_ctx():
    if RELAXED[0] is None:
        log("      (starting the second browser used for the lulustream in-player method)")
        RELAXED[0] = new_context(PW[0], relaxed=True)[1]
    return RELAXED[0]


class Catcher:
    """records the media requests of one page (all its frames) and whether anything is still loading"""

    def __init__(self, page):
        self.seen, self.inflight, self.last, self.t0 = {}, {}, time.time(), time.time()
        page.on("request", self.on_req)
        page.on("requestfinished", self.on_done)
        page.on("requestfailed", self.on_done)
        page.on("response", self.on_resp)

    def on_req(self, rq):
        try:
            if is_ad(rq.url):
                return
            self.last = time.time()
            if rq.resource_type in ("xhr", "fetch", "document", "script", "media") or is_media(rq.url):
                self.inflight[rq.url] = time.time()
            if is_media(rq.url) and rq.url not in self.seen:
                self.seen[rq.url] = {"headers": rq.all_headers(), "status": None, "t": round(time.time() - self.t0, 1),
                                     "frame": rq.frame, "frame_url": rq.frame.url}
        except Exception:
            pass

    def on_done(self, rq):
        self.inflight.pop(rq.url, None)
        self.last = time.time()

    def on_resp(self, rs):
        try:
            if rs.url in self.seen:
                self.seen[rs.url]["status"] = rs.status
        except Exception:
            pass


def click_player(page):
    best, area = None, 0
    for fr in page.frames[1:]:
        try:
            if is_ad(fr.url) or not fr.url.startswith("http"):
                continue
            box = fr.frame_element().bounding_box()
            if box and box["width"] * box["height"] > area:
                best, area = box, box["width"] * box["height"]
        except Exception:
            continue
    try:
        if best:
            page.mouse.click(best["x"] + best["width"] / 2, best["y"] + best["height"] / 2)
        else:
            vs = page.viewport_size or {"width": 1280, "height": 720}
            page.mouse.click(vs["width"] / 2, vs["height"] / 2)
    except Exception:
        pass


DEAD_RX = re.compile(r"cannot be played|error code\s*:?\s*\d{4,}|video (?:is )?(?:not found|unavailable|not available)|file (?:is )?(?:not found|was deleted|removed|doesn.t exist)|"
                     r"has been (?:removed|deleted)|no longer available|this video (?:was|has been) (?:deleted|removed)|removed (?:due|for)|copyright|"
                     r"لم يتم العثور|غير موجود|تم حذف|محذوف|تم إزالة|غير متوفر|لا يمكن تشغيل|404 not found|forbidden", re.I)
JS_DEAD = """() => { const v = document.querySelector('video'); const e = v && v.error ? ('video error ' + v.error.code) : '';
  return [e, (document.body && document.body.innerText || '').slice(0, 1500)]; }"""


def dead_server(page):
    """a host player that says the file is gone / cannot be played -> the reason, else ''"""
    for fr in page.frames:
        try:
            if "animezid" in urlparse(fr.url).netloc or fr == page.main_frame and "animezid" in fr.url:
                continue
            err, txt = fr.evaluate(JS_DEAD)
            m = DEAD_RX.search(txt or "")
            if m:
                return "player error: " + m.group(0)[:40]
            if err:
                return err
        except Exception:
            continue
    return ""


def wait_media(page, cat):
    """adaptive wait: goes on while the host is still loading (slow servers), stops at once when a valid stream shows up"""
    why, i, t0 = f"max wait {MAXWAIT:.0f}s", 0, time.time()
    while time.time() - t0 < MAXWAIT:
        page.wait_for_timeout(1000)
        i += 1
        if cancelled():
            return "cancelled"
        el = time.time() - t0
        ok = {u: d for u, d in cat.seen.items() if d["status"] in (200, 206)}
        if any(".m3u8" in u or "master" in u for u in ok) and el > 3:
            return "m3u8 caught"
        if ok and el > 8:
            return "media caught"
        if not cat.seen and i % 4 == 0:
            scan_frames(page, cat)
        if not ok and el > 2.5 and i % 2 == 0:
            d = dead_server(page)
            if d:
                return d
        if any(d.get("static") for d in cat.seen.values()) and not ok and el > 3:
            return "found in page source"
        st = {"has": False, "playing": False, "loading": False}
        for fr in page.frames:
            try:
                r = fr.evaluate(JS_VSTATE)
                for k in st:
                    st[k] = st[k] or r[k]
            except Exception:
                pass
        for u, t in list(cat.inflight.items()):
            if time.time() - t > 40:
                cat.inflight.pop(u, None)
        if not (cat.inflight or st["loading"] or time.time() - cat.last < IDLE) and el > IDLE:
            return f"idle {IDLE:.0f}s (nothing loading)"
        if not st["playing"]:
            for fr in page.frames:
                try:
                    fr.evaluate(JS_PLAY)
                except Exception:
                    pass
            if i in (2, 5, 9, 14, 20, 28, 38, 50, 62) and not cat.seen:
                click_player(page)
    return why


def close(page):
    try:
        page.close()
    except Exception:
        pass


def scan_frames(page, cat):
    """links the player holds in its JS state / page source even if it never requested them (e.g. blocked by its anti-adblock wall)"""
    n = 0
    for fr in page.frames:
        try:
            if not fr.url.startswith("http") or is_ad(fr.url):
                continue
            cands = [urljoin(fr.url, u) for u in (fr.evaluate(JS_SCAN) or [])] + find_in_text(fr.content(), fr.url)
        except Exception:
            continue
        for u in cands:
            if is_media(u) and u not in cat.seen:
                cat.seen[u] = {"headers": {}, "status": None, "t": round(time.time() - cat.t0, 1), "frame": fr, "frame_url": fr.url, "static": True}
                n += 1
    return n


def wall_seen(page):
    for fr in page.frames:
        try:
            if WALL_RX.search(fr.evaluate(JS_WALL) or ""):
                return True
        except Exception:
            continue
    return False


# ================================================================= MegaMax mirrors
def get_mirrors(ctx, url):
    last = None
    for attempt in range(3):
        page = ctx.new_page()
        try:
            page.goto(url, wait_until="domcontentloaded", timeout=60000)
            for _ in range(30):
                if "just a moment" not in (page.title() or "").lower():
                    break
                page.wait_for_timeout(1000)
            page.wait_for_timeout(1500)
            res = page.evaluate(JS_INERTIA, page.url)
            if res["status"] == 200:
                d = json.loads(res["text"])["props"]["streams"]
                if d.get("data"):
                    return d, res.get("name") or ""
            last = f"status {res['status']}"
        except Exception as e:
            last = str(e).splitlines()[0]
        finally:
            close(page)
        time.sleep(2)
    raise RuntimeError(f"could not read the mirror list ({last})")


# ================================================================= AnimeZid watch page
def press_overlay(page):
    for pat in (r"اضغط هنا لتشغيل", r"تشغيل الحلقة", r"^\s*(?:play|شغل|شاهد الآن|مشاهدة الآن)\s*$"):
        try:
            loc = page.get_by_text(re.compile(pat, re.I)).first
            if loc.count():
                try:
                    loc.click(timeout=2500)
                except Exception:
                    loc.dispatch_event("click")
                return True
        except Exception:
            continue
    return False


def list_servers(page, seconds=10):
    end = time.time() + seconds
    while True:
        try:
            found = page.evaluate(JS_SERVERS, {"rx": SERVER_RX})
        except Exception:
            found = []
        uniq = {}
        for r in found:
            uniq.setdefault(r["name"].lower(), r)
        items = [(page.locator(f'[data-hx="{r["idx"]}"]').first, r["name"]) for r in uniq.values()]
        if items or time.time() >= end:
            return items
        page.wait_for_timeout(700)


def play_url_of(url):
    u = urlparse(url)
    vid = (parse_qs(u.query).get("vid") or [""])[0]
    return f"{u.scheme}://{u.netloc}/play.php?vid={vid}"


SESS_ERR_RX = re.compile(r"تعذر التحقق من جلسة|حدّث الصفحة|حدث الصفحة|verify.{0,20}session", re.I)


def session_err(page):
    try:
        return bool(SESS_ERR_RX.search(page.evaluate("() => (document.body && document.body.innerText || '').slice(0, 4000)") or ""))
    except Exception:
        return False


def first_click(page):
    """The very first click on the player (the 'press here to play' cover) - AnimeZid needs it BEFORE any server is chosen,
    otherwise it answers 'could not verify the browser session'."""
    try:                                       # a little human-like mouse movement first
        for x, y in ((300, 260), (640, 340), (900, 420)):
            page.mouse.move(x, y, steps=8)
            page.wait_for_timeout(120)
    except Exception:
        pass
    if press_overlay(page):
        return True
    try:
        el = page.query_selector("[data-player-iframe], iframe, video, .player, #player")
        bb = el.bounding_box() if el else None
        if bb:
            page.mouse.click(bb["x"] + bb["width"] / 2, bb["y"] + bb["height"] / 2)
            return True
        page.mouse.click(640, 360)
        return True
    except Exception:
        return False


def dump_session_error(page, net):
    try:
        d = os.path.join(HERE, "mmgrab_debug")
        os.makedirs(d, exist_ok=True)
        with open(os.path.join(d, "session_error.html"), "w", encoding="utf-8") as f:
            f.write(page.content())
        with open(os.path.join(d, "session_error_requests.json"), "w", encoding="utf-8") as f:
            json.dump(net[-60:], f, ensure_ascii=False, indent=1)
        cookies = [{"name": c["name"], "domain": c["domain"]} for c in page.context.cookies()]
        with open(os.path.join(d, "session_error_cookies.json"), "w", encoding="utf-8") as f:
            json.dump(cookies, f, indent=1)
        log("      saved diagnostics to", d)
    except Exception:
        pass


def open_play(ctx, play_url):
    page = ctx.new_page()
    net = []
    page.on("response", lambda r: net.append({"url": r.url[:200], "status": r.status, "type": r.request.resource_type})
            if "animezid" in r.url and r.request.resource_type in ("xhr", "fetch", "document") else None)
    items = []
    saved_adblock = ADBLOCK[0]
    try:
        for attempt in range(4):
            try:
                if attempt == 0:
                    page.goto(play_url, wait_until="domcontentloaded", timeout=60000, referer=AZ_REFERER)
                else:
                    log("      page asked for a refresh (session check) - reloading" + (" without ad blocking" if attempt == 3 else ""))
                    if attempt == 3:
                        ADBLOCK[0] = False
                    page.wait_for_timeout(1500 * attempt)
                    page.reload(wait_until="domcontentloaded", timeout=60000)
            except Exception as e:
                log("      watch page did not load:", str(e).splitlines()[0])
            page.wait_for_timeout(2500)
            first_click(page)                   # click the player first, even though the server list is already visible
            page.wait_for_timeout(1500)
            if session_err(page):
                if attempt == 3:
                    dump_session_error(page, net)
                continue
            items = list_servers(page, 8)
            if items:
                break
    finally:
        ADBLOCK[0] = saved_adblock
    return page, items


def megamax_in(page):
    for fr in page.frames:
        if re.search(r"(megamax|share4max)[^/]*/iframe/[A-Za-z0-9]{8,}", fr.url) or re.search(r"/iframe/[A-Za-z0-9]{8,}/?$", urlparse(fr.url).path):
            if "animezid" not in urlparse(fr.url).netloc:
                return fr.url
    for src in (page.evaluate(JS_IFRAMES) or []):
        if re.search(r"(megamax|share4max)[^/]*/iframe/[A-Za-z0-9]{8,}", src):
            return "https:" + src if src.startswith("//") else src
    return None


def find_megamax(ctx, play_url):
    """-> (megamax iframe url | None, [outer server names in page order, MegaMax removed])"""
    page, items = open_play(ctx, play_url)
    names = [n for _, n in items]
    mega_url = None
    reqs = []
    page.on("request", lambda rq: reqs.append(rq.url) if re.search(r"(megamax|share4max)[^/]*/iframe/", rq.url) else None)
    try:
        mm = next((loc for loc, n in items if "mega" in n.lower()), None)
        if mm is not None:
            mega_url = megamax_in(page)          # the page may already have auto-selected it
            if not mega_url:
                try:
                    mm.click(timeout=5000)
                except Exception:
                    mm.dispatch_event("click")
            for k in range(24):
                mega_url = mega_url or megamax_in(page) or next((u for u in reqs if "/iframe/" in u), None)
                if mega_url:
                    break
                if k in (6, 14) and session_err(page):          # "could not verify the browser session": reload, click the player, choose again
                    page.reload(wait_until="domcontentloaded", timeout=60000)
                    page.wait_for_timeout(1500)
                    first_click(page)
                    page.wait_for_timeout(1500)
                    again = next((l for l, n in list_servers(page, 6) if "mega" in n.lower()), None)
                    if again is not None:
                        try:
                            again.click(timeout=5000)
                        except Exception:
                            again.dispatch_event("click")
                page.wait_for_timeout(500)
    finally:
        title = ""
        try:
            title = page.title()
        except Exception:
            pass
        close(page)
    outer = [n for n in names if "mega" not in n.lower()]
    return mega_url, outer, title


EP_RX = re.compile(r"(?:الحلقة|حلقة|الحلقه|حلقه|episode|ep)[\s\-]*(\d+(?:\.\d+)?)", re.I)


def num_str(x):
    x = float(x)
    return str(int(x)) if x == int(x) else str(x)


def ep_number(*texts):
    """episode number found in a page title / file name (Arabic or English), as '1', '2' ... or None"""
    for t in texts:
        for rx in (EP_RX, re.compile(r"S\d+E(\d+)", re.I), re.compile(r"\bE(\d{1,4})\b")):
            m = rx.search(t or "")
            if m:
                return num_str(m.group(1))
    return None


def collect_episodes(ctx, url):
    page = ctx.new_page()
    eps, ep_rx = {}, EP_RX
    u = urlparse(url)
    slug = (re.match(r"/series/([^/]+)", unquote(u.path)) or [None, "series"])[1]

    def anchors(link):
        try:
            page.goto(link, wait_until="domcontentloaded", timeout=60000, referer=AZ_REFERER)
            page.wait_for_timeout(1200)
            return page.evaluate(JS_ANCHORS) or []
        except Exception as e:
            log("   could not load", link, str(e).splitlines()[0])
            return []
    try:
        first = anchors(url)
        base = f"{u.scheme}://{u.netloc}"
        if re.fullmatch(r"/series/[^/]+/season/\d+/?", unquote(u.path)):
            seasons = [(int(re.search(r"season/(\d+)", u.path).group(1)), url.split("?")[0])]
        else:
            ss = {}
            for a in first:
                m = re.fullmatch(r"/series/[^/]+/season/(\d+)/?", unquote(urlparse(a["href"].split("?")[0]).path))
                if m:
                    ss[int(m.group(1))] = a["href"].split("?")[0].split("#")[0]
            seasons = sorted(ss.items()) or [(1, url.split("?")[0])]
        if SEASONS:
            seasons = [s for s in seasons if s[0] in SEASONS]
        for sn, surl in seasons:
            for pg in range(1, 60):
                rows = anchors(surl if pg == 1 else f"{surl}?page={pg}")
                new = 0
                for a in rows:
                    p = urlparse(a["href"])
                    vid = (parse_qs(p.query).get("vid") or [""])[0]
                    if "watch.php" not in p.path or not vid or re.search(r"التالية|السابقة", a["text"]) or vid in eps:
                        continue
                    m = ep_rx.search(a["text"]) or ep_rx.search(a["title"])
                    if m:
                        eps[vid] = {"vid": vid, "season": sn, "num": float(m.group(1)), "href": f"{base}/play.php?vid={vid}"}
                        new += 1
                log(f"   season {sn} page {pg}: {new} new episode(s)")
                if not new:
                    break
    finally:
        close(page)
    out = sorted(eps.values(), key=lambda e: (e["season"], e["num"]))
    out = [e for e in out if (EP_FROM is None or e["num"] >= EP_FROM) and (EP_TO is None or e["num"] <= EP_TO)]
    multi = len({e["season"] for e in out}) > 1
    for e in out:
        e["label"] = num_str(e["num"])                      # 1, 2, 3 ... (12.5 for a special) - no zero padding, no words
        e["sub"] = f"S{e['season']}" if multi else ""       # only when several seasons are collected together: one folder per season
    return out


# ================================================================= verification + python download
def get(url, h, **kw):
    return requests.get(url, headers=h, timeout=kw.pop("timeout", 20), **kw)


def best_variant(master_url, txt):
    best, bw = None, -1
    lines = txt.splitlines()
    for i, l in enumerate(lines):
        if l.startswith("#EXT-X-STREAM-INF"):
            m = re.search(r"BANDWIDTH=(\d+)", l)
            b = int(m.group(1)) if m else 0
            nxt = next((x.strip() for x in lines[i + 1:] if x.strip() and not x.startswith("#")), None)
            if nxt and b > bw:
                best, bw = urljoin(master_url, nxt), b
    return best


def header_variants(browser_headers, embed, frame_url=None):
    skip = {"host", "content-length", "accept-encoding", "connection", "range", "if-range"}
    v = []
    if browser_headers:
        v.append(("browser-exact", {k: x for k, x in browser_headers.items() if k.lower() not in skip}))
    for name, ref in (("frame-referer", frame_url), ("embed-referer", embed), ("megamax-referer", MEGA_REFERER), ("animezid-referer", AZ_REFERER)):
        if ref and ref.startswith("http"):
            o = urlparse(ref)
            v.append((name, {"User-Agent": UA, "Referer": ref, "Origin": f"{o.scheme}://{o.netloc}"}))
    v.append(("ua-only", {"User-Agent": UA}))
    return v


def verify(url, browser_headers, embed, frame_url=None):
    why = []
    for name, h in header_variants(browser_headers, embed, frame_url):
        try:
            if re.search(r"\.m3u8|master|/hls", url.lower()):
                r = get(url, h)
                if r.status_code != 200 or not r.text.lstrip().startswith("#EXTM3U"):
                    why.append(f"{name}: {r.status_code}")
                    continue
                txt, purl = r.text, url
                if "#EXT-X-STREAM-INF" in txt:
                    bv = best_variant(url, txt)
                    r2 = get(bv, h)
                    if r2.status_code != 200:
                        why.append(f"{name}: variant {r2.status_code}")
                        continue
                    txt, purl = r2.text, bv
                minutes = sum(float(x) for x in re.findall(r"#EXTINF:([\d.]+)", txt)) / 60
                segs = [l.strip() for l in txt.splitlines() if l.strip() and not l.startswith("#")]
                if not segs:
                    why.append(f"{name}: empty playlist")
                    continue
                r3 = get(urljoin(purl, segs[0]), h, stream=True)
                ok_seg = r3.status_code in (200, 206)
                r3.close()
                if not ok_seg:
                    why.append(f"{name}: first segment {r3.status_code}")
                    continue
                if minutes < MIN_MIN:
                    return {"ok": False, "why": f"only {minutes:.1f} min (decoy/preview?)", "minutes": minutes}
                return {"ok": True, "kind": "hls", "url": purl, "master": url, "headers": h, "minutes": round(minutes, 1), "hdr_variant": name}
            h2 = dict(h)
            h2["Range"] = "bytes=0-1023"
            r = get(url, h2, stream=True)
            total = int((r.headers.get("Content-Range") or "/0").split("/")[-1] or 0) or int(r.headers.get("Content-Length") or 0)
            ct = (r.headers.get("Content-Type") or "").lower()
            r.close()
            if r.status_code not in (200, 206) or ("video" not in ct and "octet" not in ct):
                why.append(f"{name}: {r.status_code} {ct}")
                continue
            if total < max(2 << 20, MIN_MIN * 60 * 60000):
                return {"ok": False, "why": f"file too small ({total >> 20} MB)", "minutes": 0}
            return {"ok": True, "kind": "mp4", "url": url, "headers": h, "minutes": 0, "size": total, "hdr_variant": name}
        except Exception as e:
            why.append(f"{name}: {type(e).__name__}")
    return {"ok": False, "why": "; ".join(why) or "no header set worked"}


class Meter:
    def __init__(self, total):
        self.total, self.n, self.bytes, self.t0, self.last = total, 0, 0, time.time(), 0.0
        self.lock = threading.Lock()
        self.entry = getattr(TL, "entry", None)      # captured here: add() is called from worker threads

    def add(self, size):
        with self.lock:
            self.n += 1
            self.bytes += size
            now = time.time()
            if now - self.last > 0.5 or self.n >= self.total:
                self.last = now
                text = f"{self.n}/{self.total} · {self.bytes / 1e6:.0f} MB · {self.bytes / max(now - self.t0, .01) / 1e6:.1f} MB/s"
                if self.entry is not None:
                    with LOCK:
                        self.entry.update(prog=text, status="downloading")
                else:
                    print("\r   " + text + "   ", end="", flush=True)


def ffmpeg_ok():
    if not shutil.which("ffmpeg"):
        log("   ffmpeg not found on PATH (needed for HLS). Install it from https://ffmpeg.org")
        return False
    return True


def download_hls(url, h, out, workers):
    if not ffmpeg_ok():
        return False
    txt = get(url, h).text
    tmp = out + ".parts"
    os.makedirs(tmp, exist_ok=True)
    jobs, lines, n = [], [], 0
    for raw in txt.splitlines():
        s = raw.strip()
        if s.startswith(("#EXT-X-KEY", "#EXT-X-MAP")):
            m = re.search(r'URI="([^"]+)"', s)
            if m:
                n += 1
                name = f"aux{n}" + (".mp4" if s.startswith("#EXT-X-MAP") else ".key")
                jobs.append((urljoin(url, m.group(1)), name))
                s = s.replace(m.group(1), name)
            lines.append(s)
        elif s and not s.startswith("#"):
            n += 1
            ext = os.path.splitext(urlparse(s).path)[1].lower()
            name = f"seg{n:06d}" + (ext if ext in (".ts", ".m4s", ".mp4", ".aac", ".m4a", ".cmfv", ".cmfa") else ".ts")
            jobs.append((urljoin(url, s), name))
            lines.append(name)
        else:
            lines.append(s)
    meter, store = Meter(len(jobs)), threading.local()
    cjob = getattr(TL, "job", None)

    def stop():
        return bool(cjob and cjob.get("cancel"))

    def one(job):
        u, name = job
        if stop():
            return False
        path = os.path.join(tmp, name)
        if os.path.exists(path) and os.path.getsize(path) > 0:
            meter.add(os.path.getsize(path))
            return True
        for attempt in range(6):
            try:
                if not hasattr(store, "s"):
                    store.s = requests.Session()
                    store.s.trust_env = False
                r = store.s.get(u, headers=h, timeout=(10, 40), stream=True)
                r.raise_for_status()
                size = 0
                with open(path + ".part", "wb") as f:
                    for chunk in r.iter_content(1 << 18):
                        f.write(chunk)
                        size += len(chunk)
                os.replace(path + ".part", path)
                meter.add(size)
                return True
            except Exception:
                time.sleep(min(0.4 * 2 ** attempt, 6))
        return False
    with ThreadPoolExecutor(max_workers=workers) as ex:
        ok = list(ex.map(one, jobs))
    if meter.entry is None:
        print()
    if stop():
        log("   cancelled")
        return False
    if not all(ok):
        log(f"   {ok.count(False)} segment(s) failed; partial files kept in {tmp} (running again resumes them)")
        return False
    local = os.path.join(tmp, "local.m3u8")
    open(local, "w", encoding="utf-8").write("\n".join(lines) + "\n")
    base = ["ffmpeg", "-y", "-hide_banner", "-loglevel", "error", "-allowed_extensions", "ALL", "-protocol_whitelist", "file,crypto,data", "-i", local, "-c", "copy"]
    for extra in (["-bsf:a", "aac_adtstoasc"], []):
        if subprocess.call(base + extra + ["-movflags", "+faststart", out]) == 0:
            shutil.rmtree(tmp, ignore_errors=True)
            return True
    return False


def download_file(url, h, out):
    entry, cjob = getattr(TL, "entry", None), getattr(TL, "job", None)
    with get(url, h, stream=True, timeout=30) as r:
        r.raise_for_status()
        total, done, t0, last = int(r.headers.get("Content-Length") or 0), 0, time.time(), 0.0
        with open(out + ".part", "wb") as f:
            for chunk in r.iter_content(1 << 20):
                if cjob and cjob.get("cancel"):
                    raise RuntimeError("cancelled")
                f.write(chunk)
                done += len(chunk)
                if time.time() - last > 0.5:
                    last = time.time()
                    text = f"{done >> 20}" + (f"/{total >> 20}" if total else "") + f" MB · {done / max(time.time() - t0, .01) / 1e6:.1f} MB/s"
                    if entry is not None:
                        with LOCK:
                            entry.update(prog=text, status="downloading")
                    else:
                        print("\r   " + text + "   ", end="", flush=True)
    if entry is None:
        print()
    os.replace(out + ".part", out)
    return True


# ================================================================= browser download (lulustream's own method)
def join_parts(tmp, out):
    parts = sorted(f for f in os.listdir(tmp) if f.endswith(".part"))
    joined = os.path.join(tmp, "all.bin")
    with open(joined, "wb") as w:
        for f in parts:
            with open(os.path.join(tmp, f), "rb") as r:
                shutil.copyfileobj(r, w)
    for extra in (["-bsf:a", "aac_adtstoasc"], []):
        r = subprocess.run(["ffmpeg", "-y", "-loglevel", "error", "-i", joined, "-c", "copy"] + extra + ["-movflags", "+faststart", out], capture_output=True, text=True)
        if r.returncode == 0 and os.path.exists(out) and os.path.getsize(out) > 0:
            shutil.rmtree(tmp, ignore_errors=True)
            return True
    log("      ffmpeg could not join the segments:", (r.stderr or "").strip()[:200])
    shutil.rmtree(tmp, ignore_errors=True)
    return False


def browser_download(page, frame, url, out, why_out):
    """segments are fetched by JavaScript running inside the player frame, handed to python, joined by ffmpeg. -> True/False"""
    if not ffmpeg_ok():
        return False
    parts = os.path.abspath(out) + ".parts"
    os.makedirs(parts, exist_ok=True)
    have = sorted(int(f[:7]) - 1 for f in os.listdir(parts) if f.endswith(".part") and f[:7].isdigit())
    job = {"dir": parts, "bytes": 0}
    JOBS[page] = job
    for f in page.frames:
        try:
            f.evaluate(JS_PAUSE)          # the tab's own player must not compete for the connection
        except Exception:
            pass
    cfg = {"url": url, "conc": opt("dl-conc", 4, int), "have": have, "retries": 8, "backoff": 0.5, "minsec": MIN_MIN * 60}
    try:
        frame.evaluate("(cfg) => { (" + JS_HLS_DL + ")(cfg); }", cfg)
    except Exception as e:
        why_out.append("could not start in-player download: " + str(e).splitlines()[0])
        return False
    if have:
        log(f"      resuming: {len(have)} segment(s) already saved")
    last_n, last_t, last_print, t0 = -1, time.time(), 0.0, time.time()
    try:
        while True:
            page.wait_for_timeout(1000)           # also lets python receive the segments (exposed binding)
            if cancelled():
                why_out.append("cancelled")
                return False
            try:
                st = frame.evaluate("() => window.__mmp")
            except Exception:
                why_out.append("the player frame closed during the download")
                return False
            if not st:
                why_out.append("download script not running")
                return False
            if st.get("err"):
                why_out.append(st["err"])
                return False
            now = time.time()
            if st["done"] != last_n:
                last_n, last_t = st["done"], now
                set_entry(prog=f"{st['done']}/{st.get('total', 0)} · {job['bytes'] / 1e6:.0f} MB (in-player)", status="downloading")
            elif now - last_t > 60:
                why_out.append("no progress for 60 s")
                return False
            if now - last_print > 8 and st.get("total"):
                last_print = now
                slow = f", CDN dropped {st['fails']} request(s) -> {st['limit']} parallel" if st.get("fails") else ""
                log(f"      {st['done']}/{st['total']} segments, {job['bytes'] / 1e6:.0f} MB this session{slow}")
            if st["state"] == "done":
                break
    finally:
        JOBS.pop(page, None)
    ok = join_parts(parts, out)
    if not ok:
        why_out.append("joining failed")
    else:
        mb, dt = os.path.getsize(out) / 1e6, max(time.time() - t0, .001)
        log(f"      in-player download: {mb:.0f} MB in {dt:.0f}s ({mb / dt:.1f} MB/s)")
    return ok


# ================================================================= one step of the plan
def step_mega(ctx, c, out, att):
    for blocked in (True, False):
        ADBLOCK[0] = blocked
        try:
            res, retry = _step_mega(ctx, c, out, att)
        finally:
            ADBLOCK[0] = True
        if res or not retry:
            return res
        log("      anti-adblock wall and nothing caught -> retrying this host once without blocking (ad popups are still closed)")
        att["retried_without_adblock"] = True
    return None


def _step_mega(ctx, c, out, att):
    """-> (result | None, retry_without_blocking)"""
    if c["method"] == "browser":
        ctx = relaxed_ctx()
    page = ctx.new_page()
    cat = Catcher(page)
    info = {}
    try:
        try:
            page.goto(c["embed"], wait_until="domcontentloaded", timeout=60000, referer=MEGA_REFERER)
        except Exception as e:
            att["goto_error"] = str(e).splitlines()[0]
        att["stopped_because"] = wait_media(page, cat)
        att["waited_s"] = round(time.time() - cat.t0, 1)
        if not cat.seen:
            att["result"] = "no media"
            wall = wall_seen(page)
            att["adblock_wall"] = wall
            log(f"      nothing caught ({att['stopped_because']}, {att['waited_s']}s)" + ("  [anti-adblock wall shown]" if wall else ""))
            return None, wall and ADBLOCK[0] and not att["stopped_because"].startswith(("player error", "video error"))
        if c["method"] == "browser":                 # lulustream: no python check, the browser itself plays and downloads
            hls = [u for u in sorted(cat.seen, key=rank) if re.search(r"\.m3u8|master|/hls", u.lower()) and (cat.seen[u]["status"] == 200 or cat.seen[u].get("static"))]
            if not hls:
                att["result"] = "browser got no playlist"
                log("      the browser did not receive an HLS playlist")
                return None, False
            link = hls[0]
            log(f"      browser caught {link[:90]}")
            att["link"] = link
            if GRAB_ONLY:
                att["result"] = "ok (browser)"
                return {"kind": "hls", "url": link}, False
            why = []
            if browser_download(page, cat.seen[link]["frame"], link, out, why):
                att["result"] = "ok (browser download)"
                return {"kind": "hls", "url": link, "file": out}, False
            att["result"] = "browser download failed: " + "; ".join(why)
            log("      browser download failed:", "; ".join(why))
            return None, False
        return verify_and_download(cat, c["embed"], out, att), False
    finally:
        close(page)


def verify_and_download(cat, embed, out, att):
    for u in sorted(cat.seen, key=rank)[:3]:
        v = verify(u, cat.seen[u]["headers"], embed, cat.seen[u].get("frame_url"))
        att.setdefault("checks", []).append({"url": u, **{k: v.get(k) for k in ("ok", "why", "kind", "minutes", "hdr_variant")}})
        if not v["ok"]:
            log(f"      rejected {u[:80]}: {v.get('why')}")
            continue
        log(f"      OK {v['kind']} {v['minutes']} min (headers: {v['hdr_variant']})")
        att["link"] = v.get("master") or v["url"]
        if GRAB_ONLY:
            att["result"] = "ok"
            return {"kind": v["kind"], "url": att["link"]}

        def work(v=v):
            if v["kind"] == "hls":
                return download_hls(v["url"], v["headers"], out, WORKERS)
            return download_file(v["url"], v["headers"], out)
        pool, job, entry = getattr(TL, "pool", None), getattr(TL, "job", None), getattr(TL, "entry", None)
        if pool is not None:
            def in_pool():
                TL.job, TL.entry = job, entry
                try:
                    return bool(work())
                except Exception as e:
                    log("      download error:", (str(e).splitlines() or ["?"])[0])
                    return False
            att["result"] = "ok (download queued)"
            return {"kind": v["kind"], "url": att["link"], "file": out, "future": pool.submit(in_pool)}
        try:
            done = work()
        except Exception as e:
            done = False
            att["download_error"] = str(e).splitlines()[0]
        if done:
            att["result"] = "ok"
            return {"kind": v["kind"], "url": att["link"], "file": out}
        att["result"] = "download failed"
        log("      download failed")
        return None
    att["result"] = att.get("result") or "python cannot use the link"
    return None


def step_outer(ctx, play_url, name, out, att):
    """a server of the AnimeZid page itself (Uqload, DoodStream, VidTube ...): click its button and watch the whole page"""
    for blocked in (True, False):
        ADBLOCK[0] = blocked
        page, items = open_play(ctx, play_url)
        try:
            loc = next((l for l, n in items if n.lower() == name.lower()), None)
            if loc is None:
                att["result"] = "button not found"
                return None
            cat = Catcher(page)
            try:
                loc.click(timeout=5000)
            except Exception:
                try:
                    loc.dispatch_event("click")
                except Exception as e:
                    att["result"] = "click failed"
                    return None
            att["stopped_because"] = wait_media(page, cat)
            att["waited_s"] = round(time.time() - cat.t0, 1)
            if cat.seen:
                return verify_and_download(cat, page.url, out, att)
            dead = att["stopped_because"].startswith(("player error", "video error"))
            log(f"      nothing caught ({att['stopped_because']}){' - retrying without ad blocking' if blocked and not dead else ''}")
            if dead:
                att["result"] = att["stopped_because"]
                return None
        finally:
            close(page)
            ADBLOCK[0] = True
    att["result"] = "no media"
    return None


# ================================================================= one video
def process(ctx, src, label, report, sub="", prefix="", entry=None):
    rec = {"src": src, "label": label, "attempts": [], "ok": False}
    report.append(rec)
    TL.entry = entry
    log(f"\n=== {label or src}")
    play_url, mega_url, outer, title = None, None, [], ""
    set_entry(status="running", server="", prog="")
    if re.search(r"megamax|share4max", urlparse(src).netloc) or re.search(r"/iframe/[A-Za-z0-9]{8,}/?$", urlparse(src).path):
        mega_url = src
    else:
        play_url = play_url_of(src)
        log("   opening the AnimeZid page ...")
        mega_url, outer, title = find_megamax(ctx, play_url)
        if NO_OUTER:
            outer = []
        log("   MegaMax:", mega_url or "(not found)", "| other servers on the page:", ", ".join(outer) or "-")
    mega, name = [], ""
    if mega_url and not cancelled():
        try:
            streams, name = get_mirrors(ctx, mega_url)
            mega = build_candidates(streams)
        except Exception as e:
            rec["mirror_error"] = str(e)
            log("   MegaMax mirrors:", e)
    label = label or ep_number(title, name) or safe_name(name) or safe_name(title) or "video"
    rec["label"] = label
    out = os.path.join(OUT, safe_name(prefix) if prefix else "", sub, safe_name(label) + ".mp4")
    set_entry(file=out)
    if os.path.exists(out) and os.path.getsize(out) > 5 << 20 and not GRAB_ONLY:
        log("   already downloaded:", out)
        rec.update(ok=True, file=out, skipped=True)
        set_entry(status="skipped", prog="")
        return rec
    plan = build_plan(mega, outer if play_url else [])
    log("   plan:", " > ".join(f"{s['driver']}" + (f"({s['height']}p)" if s["height"] else "") + ("*" if s["method"] == "browser" else "") for s in plan) or "(nothing to try)")
    os.makedirs(os.path.dirname(out) or ".", exist_ok=True)
    for s in plan:
        if cancelled():
            break
        log(f"   -> {s['driver']} {s['label']}" + (f"  {s['embed']}" if s.get("embed") else "  (page server)") + ("   [in-player method]" if s["method"] == "browser" else ""))
        srv_name = f"{s['driver']} {s['label'] if s['label'] != 'page' else ''}".strip()
        set_entry(status="running", server=srv_name, prog="")
        att = {"type": s["type"], "driver": s["driver"], "quality": s["label"], "embed": s.get("embed"), "method": s["method"]}
        rec["attempts"].append(att)
        try:
            res = step_mega(ctx, s, out, att) if s["type"] == "mega" else step_outer(ctx, play_url, s["driver"], out, att)
        except Exception as e:
            att["error"] = str(e).splitlines()[0] if str(e) else repr(e)
            log("      error:", att["error"])
            res = None
        if res:
            rec.update(ok=True, link=res.get("url"), kind=res.get("kind"), host=s["driver"], file=res.get("file"))
            if res.get("future"):
                rec["future"] = res["future"]
            set_entry(server=srv_name, url=rec.get("link") or "")
            if res.get("file") and not res.get("future"):
                log(f"      saved: {res['file']}")
            return rec
    log("   all servers failed for this video" if not cancelled() else "   cancelled")
    return rec


# ================================================================= site analysis (AnimeZid structure)
def with_page(u, n):
    p = urlparse(u)
    q = [(k, v) for k, v in parse_qsl(p.query) if k != "page"]
    if n > 1:
        q.append(("page", str(n)))
    return urlunparse(p._replace(query=urlencode(q), fragment=""))


def clean_title(t):
    t = re.sub(r"\s*[\-|–—]\s*(انمي زد|أنمي زد|animezid).*$", "", t or "", flags=re.I).strip()
    return t or "video"


def _goto_anchors(page, link):
    try:
        page.goto(link, wait_until="domcontentloaded", timeout=60000, referer=AZ_REFERER)
        page.wait_for_timeout(1200)
        return page.evaluate(JS_ANCHORS) or [], page.title()
    except Exception as e:
        log("   could not load", link, (str(e).splitlines() or ["?"])[0][:100])
        return [], ""


def analyze(ctx, url):
    """what is this link?  -> {kind, title, seasons:[{n,url}], url}"""
    u = urlparse(url)
    path = unquote(u.path)
    res = {"url": url, "title": "", "seasons": [], "kind": "list"}
    if re.search(r"megamax|share4max", u.netloc) or re.search(r"/iframe/[A-Za-z0-9]{8,}/?$", path):
        res.update(kind="episode", title="MegaMax")
        return res
    if "watch.php" in path or "play.php" in path:
        vid = (parse_qs(u.query).get("vid") or [""])[0]
        res.update(kind="episode", title="video " + vid, vid=vid)
        return res
    page = ctx.new_page()
    try:
        rows, title = _goto_anchors(page, url)
        res["title"] = clean_title(title)
        m = re.match(r"/series/([^/]+)(?:/season/(\d+))?/?$", path)
        if m:
            ss = {}
            for a in rows:
                mm = re.fullmatch(r"/series/[^/]+/season/(\d+)/?", unquote(urlparse(a["href"].split("?")[0]).path))
                if mm:
                    ss[int(mm.group(1))] = a["href"].split("?")[0].split("#")[0]
            if m.group(2):
                ss.setdefault(int(m.group(2)), url.split("?")[0])
            if not ss:
                ss[1] = url.split("?")[0]
            res.update(kind="series", seasons=[{"n": n, "url": ss[n]} for n in sorted(ss)], slug=m.group(1))
            if m.group(2):
                res["selected"] = int(m.group(2))
        else:
            res["kind"] = "list"
    finally:
        close(page)
    return res


def list_items(ctx, url, season=None, max_pages=80):
    """every video link on a (season / category) page and its pages -> [{vid,num,label,season,href,title}]"""
    page = ctx.new_page()
    items, base = {}, f"{urlparse(url).scheme}://{urlparse(url).netloc}"
    try:
        for pg in range(1, max_pages + 1):
            if cancelled():
                break
            rows, _ = _goto_anchors(page, with_page(url, pg))
            new = 0
            for a in rows:
                p = urlparse(a["href"])
                vid = (parse_qs(p.query).get("vid") or [""])[0]
                if "watch.php" not in p.path or not vid or re.search(r"التالية|السابقة", a["text"]) or vid in items:
                    continue
                text = a["text"] or a["title"]
                m = EP_RX.search(text) or EP_RX.search(a["title"])
                items[vid] = {"vid": vid, "season": season, "num": float(m.group(1)) if m else None, "text": text,
                              "href": f"{base}/play.php?vid={vid}"}
                new += 1
            log(f"   {'season ' + str(season) + ' ' if season else ''}page {pg}: {new} new")
            if not new:
                break
    finally:
        close(page)
    out = list(items.values())
    if season is not None:
        out.sort(key=lambda e: (e["num"] is None, e["num"] or 0))
    for i, e in enumerate(out, 1):
        e["label"] = num_str(e["num"]) if e["num"] is not None else (safe_name(e["text"]) or str(i))
    return out


# ================================================================= studio: browser worker, jobs, server
STUDIO = {"jobs": {}, "q": queue.Queue(), "sessions": {}, "user": "", "pw_hash": b"", "salt": b"", "expires": 0, "multi": False,
          "fails": {}, "out": os.path.abspath(OUT)}


class Tee:
    def __init__(self, real):
        self.real = real

    def write(self, s):
        j = getattr(TL, "job", None)
        if j is not None and s:
            with LOCK:
                s2 = s.replace("\r", "\n")
                for line in s2.split("\n"):
                    if line.strip():
                        j["log"].append(line.rstrip())
                if len(j["log"]) > 4000:
                    del j["log"][:1000]
                    j["logbase"] += 1000
        try:
            self.real.write(s)
        except Exception:
            pass
        return len(s)

    def flush(self):
        try:
            self.real.flush()
        except Exception:
            pass

    def __getattr__(self, k):
        return getattr(self.real, k)


def new_job(kind, **params):
    jid = secrets.token_hex(6)
    j = {"id": jid, "kind": kind, "params": params, "status": "queued", "log": [], "logbase": 0, "entries": [], "result": None,
         "cancel": False, "t0": time.time(), "error": ""}
    with LOCK:
        STUDIO["jobs"][jid] = j
    STUDIO["q"].put(j)
    return j


def apply_options(o):
    global QUALITY, ONLY, NO_LULU, GRAB_ONLY, WORKERS, MIN_MIN, AVOID, NO_OUTER, MAXWAIT, IDLE
    QUALITY = str(o.get("quality") or "best")
    GRAB_ONLY = o.get("mode") == "links"
    WORKERS = max(1, min(64, int(o.get("workers") or 16)))
    MIN_MIN = float(o.get("minmin") if o.get("minmin") not in (None, "") else 10)
    NO_OUTER = not o.get("outer", True)
    AVOID = [x.strip().lower() for x in str(o.get("avoid") or "").split(",") if x.strip()]
    NO_LULU = "lulustream" in AVOID
    ONLY = [x.strip().lower() for x in str(o.get("only") or "").split(",") if x.strip()]
    MAXWAIT = float(o.get("maxwait") or MAXWAIT)
    if o.get("preferred"):
        set_preferred(o["preferred"])


def run_items(ctx, j):
    P = j["params"]
    apply_options(P.get("options") or {})
    prefix = safe_name(P.get("prefix") or "")
    items = P["items"]
    parallel = max(1, min(8, int((P.get("options") or {}).get("parallel") or 2)))
    retry = bool((P.get("options") or {}).get("retry", True))
    entries = []
    for i, it in enumerate(items):
        entries.append({"i": i, "label": it["label"], "sub": it.get("sub", ""), "season": it.get("season"), "href": it["href"],
                        "status": "waiting", "server": "", "prog": "", "file": "", "url": ""})
    j["entries"] = entries
    pool = ThreadPoolExecutor(parallel)
    TL.pool = pool
    report, pending = [], []

    def reap(block=False):
        for e, fut, rec in list(pending):
            if fut.done() or block:
                while not fut.done():
                    if j["cancel"]:
                        break
                    time.sleep(0.5)
                if not fut.done():
                    continue
                pending.remove((e, fut, rec))
                try:
                    ok = bool(fut.result())
                except Exception:
                    ok = False
                with LOCK:
                    e.update(status="done" if ok else ("cancelled" if j["cancel"] else "failed"), prog="")
                rec["ok"] = ok

    def one(e, it, rec_list):
        rec = process(ctx, it["href"], it["label"], rec_list, sub=it.get("sub", ""), prefix=prefix, entry=e)
        fut = rec.pop("future", None)
        if rec.get("skipped"):
            with LOCK:
                e["status"] = "skipped"
        elif rec["ok"] and fut is not None:
            with LOCK:
                e["status"] = "downloading"
            pending.append((e, fut, rec))
        elif rec["ok"]:
            with LOCK:
                e.update(status="done", prog="", url=rec.get("link") or "", file=rec.get("file") or e.get("file", ""))
        else:
            with LOCK:
                e["status"] = "cancelled" if j["cancel"] else "failed"
        return rec

    for e, it in zip(entries, items):
        if j["cancel"]:
            break
        one(e, it, report)
        reap()
    reap(block=True)
    if retry and not j["cancel"]:
        bad = [(e, it) for e, it in zip(entries, items) if e["status"] == "failed"]
        if bad:
            log(f"\n=== retrying {len(bad)} failed video(s) ...")
            for e, it in bad:
                if j["cancel"]:
                    break
                one(e, it, report)
                reap()
            reap(block=True)
    pool.shutdown(wait=False)
    for e in entries:
        if e["status"] == "waiting":
            e["status"] = "cancelled"
    links = [(e["label"], e.get("url")) for e in entries if e.get("url")]
    if GRAB_ONLY and links:
        os.makedirs(os.path.join(STUDIO["out"], prefix) if prefix else STUDIO["out"], exist_ok=True)
        lf = os.path.join(STUDIO["out"], prefix, "links.txt")
        with open(lf, "w", encoding="utf-8") as f:
            for lab, u in links:
                f.write(f"{lab}\t{u}\n")
        log("links written to", lf)
    for r in report:
        r.pop("future", None)
    try:
        os.makedirs(STUDIO["out"], exist_ok=True)
        with open(os.path.join(STUDIO["out"], "report_%s.json" % (prefix or "run")), "w", encoding="utf-8") as f:
            json.dump(report, f, ensure_ascii=False, indent=1, default=str)
    except Exception:
        pass
    j["result"] = {"done": sum(e["status"] == "done" for e in entries), "failed": sum(e["status"] == "failed" for e in entries),
                   "skipped": sum(e["status"] == "skipped" for e in entries), "total": len(entries)}


def do_job(ctx, j):
    P = j["params"]
    if j["kind"] == "analyze":
        j["result"] = analyze(ctx, P["url"])
    elif j["kind"] == "episodes":
        out, seen = [], set()
        base = P["url"]
        if P.get("stype") == "series":
            for s in P["seasons"]:
                if j["cancel"]:
                    break
                for e in list_items(ctx, s["url"], season=s["n"]):
                    e["sub"] = ""
                    out.append(e)
            multi = len({e["season"] for e in out}) > 1
            for e in out:
                e["sub"] = f"S{e['season']}" if multi else ""
        else:
            out = list_items(ctx, base)
        j["result"] = {"items": out}
    elif j["kind"] == "run":
        run_items(ctx, j)


def worker():
    from playwright.sync_api import sync_playwright
    p = ctx = None
    while True:
        j = STUDIO["q"].get()
        TL.job, TL.entry, TL.pool = j, None, None
        if j["cancel"]:
            j["status"] = "cancelled"
            continue
        j["status"] = "running"
        try:
            if p is None:
                p = sync_playwright().start()
            try:
                ok = ctx is not None and len(ctx.pages) >= 0
                if ok:
                    ctx.pages[0:0]
            except Exception:
                ctx = None
            if ctx is None:
                log("starting the browser ...")
                _, ctx = new_context(p)
            do_job(ctx, j)
            j["status"] = "cancelled" if j["cancel"] else "done"
        except Exception as e:
            msg = str(e).splitlines()[0] if str(e) else repr(e)
            j["error"] = msg
            j["status"] = "error"
            log("ERROR:", msg)
            if "closed" in msg.lower() or "Target" in msg:
                ctx = None
        finally:
            TL.job = TL.entry = TL.pool = None
            for pg in list(getattr(ctx, "pages", []) or [])[1:]:
                try:
                    pg.close()
                except Exception:
                    pass


def hash_pw(pw, salt):
    return hashlib.pbkdf2_hmac("sha256", pw.encode(), salt, 120000)


def make_creds():
    STUDIO["user"] = "user-" + secrets.token_hex(3)
    pw = secrets.token_urlsafe(9)
    STUDIO["salt"] = secrets.token_bytes(16)
    STUDIO["pw_hash"] = hash_pw(pw, STUDIO["salt"])
    STUDIO["expires"] = time.time() + 24 * 3600
    return STUDIO["user"], pw


def open_folder():
    os.makedirs(STUDIO["out"], exist_ok=True)
    try:
        if os.name == "nt":
            os.startfile(STUDIO["out"])
        elif sys.platform == "darwin":
            subprocess.Popen(["open", STUDIO["out"]])
        else:
            subprocess.Popen(["xdg-open", STUDIO["out"]])
        return True
    except Exception:
        return False


class H(BaseHTTPRequestHandler):
    server_version = "mmgrab"

    def log_message(self, *a):
        pass

    def _send(self, code, body, ctype="application/json; charset=utf-8", extra=None):
        data = body if isinstance(body, bytes) else (json.dumps(body, ensure_ascii=False, default=str) if ctype.startswith("application/json") else body).encode()
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(data)))
        self.send_header("Cache-Control", "no-store")
        self.send_header("X-Content-Type-Options", "nosniff")
        for k, v in (extra or {}).items():
            self.send_header(k, v)
        self.end_headers()
        self.wfile.write(data)

    def host_ok(self):
        host = (self.headers.get("Host") or "").split(":")[0]
        return host in ("127.0.0.1", "localhost")

    def authed(self):
        if time.time() > STUDIO["expires"]:
            return False
        c = SimpleCookie(self.headers.get("Cookie") or "")
        sid = c["sid"].value if "sid" in c else ""
        return bool(sid) and sid in STUDIO["sessions"]

    def body(self):
        n = int(self.headers.get("Content-Length") or 0)
        try:
            return json.loads(self.rfile.read(min(n, 1 << 20)) or b"{}")
        except Exception:
            return {}

    def do_GET(self):
        if not self.host_ok():
            return self._send(403, {"error": "host"})
        u = urlparse(self.path)
        q = {k: v for k, v in parse_qsl(u.query)}
        if u.path == "/":
            return self._send(200, HTML, "text/html; charset=utf-8")
        if not self.authed():
            return self._send(401, {"error": "login"})
        if u.path == "/api/me":
            return self._send(200, {"user": STUDIO["user"], "ffmpeg": ffmpeg_ok(), "out": STUDIO["out"],
                                    "expires_in": int(STUDIO["expires"] - time.time())})
        if u.path == "/api/job":
            j = STUDIO["jobs"].get(q.get("id"))
            if not j:
                return self._send(404, {"error": "no such job"})
            since = int(q.get("since") or 0)
            with LOCK:
                lines = j["log"][max(0, since - j["logbase"]):]
                data = {"id": j["id"], "status": j["status"], "log": lines, "next": j["logbase"] + len(j["log"]), "entries": j["entries"],
                        "result": j["result"], "error": j["error"], "elapsed": int(time.time() - j["t0"])}
                return self._send(200, data)
        self._send(404, {"error": "not found"})

    def do_POST(self):
        if not self.host_ok():
            return self._send(403, {"error": "host"})
        if self.headers.get("Origin") and urlparse(self.headers["Origin"]).netloc.split(":")[0] not in ("127.0.0.1", "localhost"):
            return self._send(403, {"error": "origin"})
        u = urlparse(self.path)
        b = self.body()
        if u.path == "/api/login":
            ip = self.client_address[0]
            now = time.time()
            fl = [t for t in STUDIO["fails"].get(ip, []) if now - t < 60]
            if len(fl) >= 5:
                return self._send(429, {"error": "too many attempts, wait a minute"})
            ok = (time.time() < STUDIO["expires"] and hmac.compare_digest(str(b.get("u", "")), STUDIO["user"])
                  and hmac.compare_digest(hash_pw(str(b.get("p", "")), STUDIO["salt"]), STUDIO["pw_hash"]))
            if not ok:
                fl.append(now)
                STUDIO["fails"][ip] = fl
                return self._send(401, {"error": "wrong username or password"})
            if not STUDIO["multi"]:
                STUDIO["sessions"].clear()
            sid = secrets.token_urlsafe(24)
            STUDIO["sessions"][sid] = now
            return self._send(200, {"ok": True}, extra={"Set-Cookie": f"sid={sid}; HttpOnly; SameSite=Strict; Path=/; Max-Age=86400"})
        if not self.authed():
            return self._send(401, {"error": "login"})
        if u.path == "/api/task":
            kind = b.get("kind")
            if kind not in ("analyze", "episodes", "run"):
                return self._send(400, {"error": "bad kind"})
            busy = [x for x in STUDIO["jobs"].values() if x["kind"] == "run" and x["status"] in ("queued", "running")]
            if kind == "run" and busy:
                return self._send(409, {"error": "a download is already running"})
            params = {k: v for k, v in b.items() if k != "kind"}
            return self._send(200, {"id": new_job(kind, **params)["id"]})
        if u.path == "/api/cancel":
            j = STUDIO["jobs"].get(b.get("id"))
            if j:
                j["cancel"] = True
            return self._send(200, {"ok": bool(j)})
        if u.path == "/api/open":
            return self._send(200, {"ok": open_folder(), "path": STUDIO["out"]})
        if u.path == "/api/logout":
            STUDIO["sessions"].clear()
            return self._send(200, {"ok": True})
        self._send(404, {"error": "not found"})


def studio(argv):
    port = opt("port", 8765, int)
    STUDIO["multi"] = "--multi" in argv
    STUDIO["out"] = os.path.abspath(OUT)
    srv = None
    for pt in range(port, port + 20):
        try:
            srv = ThreadingHTTPServer(("127.0.0.1", pt), H)
            port = pt
            break
        except OSError:
            continue
    if srv is None:
        sys.exit("no free port")
    sys.stdout = Tee(sys.stdout)
    user, pw = make_creds()
    threading.Thread(target=worker, daemon=True).start()
    url = f"http://127.0.0.1:{port}/"
    print("=" * 56)
    print("  mmgrab studio")
    print("  address  :", url)
    print("  username :", user)
    print("  password :", pw)
    print("  valid for 24 hours (kept in memory only)")
    print("  downloads:", STUDIO["out"])
    print("=" * 56, flush=True)
    if "--no-open" not in argv:
        threading.Timer(0.8, lambda: webbrowser.open(url)).start()
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        print("\nbye")



HTML = r"""<!doctype html>
<html lang="ar" dir="rtl">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>mmgrab studio</title>
<style>
:root{--bg:#0f1220;--card:#181c30;--line:#2a3050;--tx:#e8ebf7;--mut:#8f97b8;--ac:#6c8cff;--ok:#38c172;--bad:#ef5b5b;--warn:#f0b429}
*{box-sizing:border-box}
body{margin:0;background:var(--bg);color:var(--tx);font-family:Segoe UI,Tahoma,Arial,sans-serif;font-size:15px}
.wrap{max-width:1000px;margin:0 auto;padding:18px 14px 60px}
h1{font-size:20px;margin:0 0 4px}
.sub{color:var(--mut);font-size:13px;margin-bottom:16px}
.card{background:var(--card);border:1px solid var(--line);border-radius:12px;padding:14px;margin-bottom:14px}
.card h2{font-size:15px;margin:0 0 10px;color:var(--ac)}
input[type=text],input[type=password],input[type=number],select{background:#0f1325;border:1px solid var(--line);color:var(--tx);border-radius:8px;padding:9px 10px;font-size:14px;width:100%}
input[dir=ltr]{direction:ltr;text-align:left}
button{background:var(--ac);color:#fff;border:0;border-radius:8px;padding:9px 16px;font-size:14px;cursor:pointer}
button.sec{background:#2a3050}
button.bad{background:var(--bad)}
button:disabled{opacity:.5;cursor:default}
.row{display:flex;gap:8px;align-items:center;flex-wrap:wrap}
.row>.grow{flex:1;min-width:200px}
.chips{display:flex;gap:8px;flex-wrap:wrap}
.chip{border:1px solid var(--line);border-radius:20px;padding:6px 14px;cursor:pointer;user-select:none;background:#0f1325}
.chip.on{background:var(--ac);border-color:var(--ac)}
.grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(210px,1fr));gap:10px}
.grid label{font-size:13px;color:var(--mut);display:block;margin-bottom:4px}
.eplist{max-height:320px;overflow:auto;border:1px solid var(--line);border-radius:8px;padding:6px;display:grid;grid-template-columns:repeat(auto-fill,minmax(110px,1fr));gap:4px;margin-top:8px}
.ep{padding:5px 8px;border-radius:6px;background:#0f1325;cursor:pointer;font-size:13px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis;border:1px solid transparent}
.ep.on{border-color:var(--ac);background:#1d2650}
table{width:100%;border-collapse:collapse;font-size:13px}
th,td{padding:6px 8px;border-bottom:1px solid var(--line);text-align:right}
td.n{direction:ltr;text-align:left}
.st{font-weight:600}
.st.done{color:var(--ok)}.st.failed{color:var(--bad)}.st.running,.st.downloading{color:var(--ac)}.st.skipped,.st.cancelled{color:var(--warn)}.st.waiting{color:var(--mut)}
pre{background:#0a0d1a;border:1px solid var(--line);border-radius:8px;padding:10px;max-height:300px;overflow:auto;direction:ltr;text-align:left;font-size:12px;white-space:pre-wrap;margin:8px 0 0}
.mut{color:var(--mut);font-size:13px}
.err{color:var(--bad);margin-top:8px}
.hide{display:none}
.bar{height:8px;background:#0f1325;border-radius:6px;overflow:hidden;margin:8px 0}
.bar>i{display:block;height:100%;background:var(--ok);width:0}
</style>
</head>
<body>
<div class="wrap">
<h1>mmgrab studio</h1>
<div class="sub">تحميل حلقات AnimeZid عبر سيرفرات MegaMax وغيرها &mdash; يعمل محليا على جهازك فقط</div>

<div id="loginBox" class="card hide">
  <h2>تسجيل الدخول</h2>
  <div class="mut" style="margin-bottom:8px">اسم المستخدم وكلمة السر مكتوبان في نافذة الترمنال (صالحان 24 ساعة).</div>
  <div class="grid">
    <div><label>اسم المستخدم</label><input type="text" id="lu" dir="ltr" autocomplete="off"></div>
    <div><label>كلمة السر</label><input type="password" id="lp" dir="ltr" autocomplete="off"></div>
  </div>
  <div class="row" style="margin-top:10px"><button id="loginBtn">دخول</button></div>
  <div class="err" id="loginErr"></div>
</div>

<div id="app" class="hide">
  <div class="card">
    <h2>1) رابط المسلسل</h2>
    <div class="row">
      <input class="grow" type="text" id="url" dir="ltr" placeholder="https://animezid.org/series/boruto-ar/  (مسلسل / موسم / فئة أفلام / حلقة)">
      <button id="anBtn">تحليل</button>
    </div>
    <div class="mut" id="anMsg" style="margin-top:8px"></div>
  </div>

  <div class="card hide" id="seasonCard">
    <h2>2) المواسم</h2>
    <div class="chips" id="seasons"></div>
    <div class="row" style="margin-top:10px">
      <button class="sec" id="allS">كل المواسم</button>
      <button class="sec" id="noS">لا شيء</button>
      <button id="loadEps">عرض الحلقات</button>
    </div>
  </div>

  <div class="card hide" id="epCard">
    <h2>3) الحلقات <span class="mut" id="epCount"></span></h2>
    <div class="row">
      <input type="text" id="flt" placeholder="بحث / فلتر" style="max-width:180px">
      <span class="mut">من</span><input type="number" id="rf" style="max-width:90px">
      <span class="mut">إلى</span><input type="number" id="rt" style="max-width:90px">
      <button class="sec" id="rngBtn">حدد النطاق</button>
      <button class="sec" id="allE">الكل</button>
      <button class="sec" id="noE">لا شيء</button>
    </div>
    <div class="eplist" id="eps"></div>
  </div>

  <div class="card hide" id="optCard">
    <h2>4) الإعدادات</h2>
    <div class="grid">
      <div><label>الوضع</label><select id="o_mode"><option value="download">تحميل الفيديوهات</option><option value="links">جلب الروابط فقط</option></select></div>
      <div><label>الجودة</label><select id="o_quality"><option value="best">الأعلى</option><option value="1080">حتى 1080</option><option value="720">حتى 720</option><option value="480">حتى 480</option></select></div>
      <div><label>تحميلات متزامنة</label><input type="number" id="o_parallel" value="2" min="1" max="8"></div>
      <div><label>اتصالات لكل تحميل</label><input type="number" id="o_workers" value="16" min="1" max="64"></div>
      <div><label>أقل مدة مقبولة (دقيقة، 0 = إيقاف)</label><input type="number" id="o_minmin" value="10" min="0"></div>
      <div><label>ترتيب المفضلة (بالترتيب)</label><input type="text" id="o_pref" dir="ltr" value="streamhg,byse,uqload"></div>
      <div><label>سيرفرات تجنبها (مفصولة بفاصلة)</label><input type="text" id="o_avoid" dir="ltr" placeholder="مثال: lulustream"></div>
      <div><label>اسم مجلد التحميل</label><input type="text" id="o_prefix"></div>
    </div>
    <div class="row" style="margin-top:10px">
      <label><input type="checkbox" id="o_outer" checked> جرّب سيرفرات الصفحة الأخرى (Uqload, DoodStream ...) عند فشل MegaMax</label>
    </div>
    <div class="row" style="margin-top:6px">
      <label><input type="checkbox" id="o_retry" checked> أعد محاولة الفاشل مرة أخرى في النهاية</label>
    </div>
    <div class="row" style="margin-top:12px">
      <button id="runBtn">ابدأ</button>
      <span class="mut" id="runInfo"></span>
    </div>
  </div>

  <div class="card hide" id="runCard">
    <h2>التنفيذ <span class="mut" id="runStat"></span></h2>
    <div class="bar"><i id="bar"></i></div>
    <div class="row">
      <button class="bad" id="stopBtn">إيقاف</button>
      <button class="sec" id="openBtn">فتح مجلد التحميل</button>
      <span class="mut" id="outPath"></span>
    </div>
    <div style="overflow:auto;margin-top:10px"><table><thead><tr><th>#</th><th>الحلقة</th><th>الحالة</th><th>السيرفر</th><th>التقدم</th></tr></thead><tbody id="rows"></tbody></table></div>
    <pre id="log"></pre>
  </div>
  <div class="mut" id="ffwarn"></div>
</div>
</div>

<script>
const $=id=>document.getElementById(id);
const ST={done:'تم',failed:'فشل',running:'يعمل',downloading:'يحمّل',skipped:'موجود',cancelled:'أُلغي',waiting:'ينتظر'};
let A=null, items=[], sel=new Set(), seasonsSel=new Set(), curJob=null, poll=null;

async function api(path, body){
  const r = await fetch(path, body===undefined ? {} : {method:'POST', headers:{'Content-Type':'application/json'}, body:JSON.stringify(body)});
  let j = {}; try{ j = await r.json(); }catch(e){}
  if(r.status===401 && path!=='/api/login'){ show(false); }
  return {ok:r.ok, status:r.status, j};
}
function show(logged){ $('loginBox').classList.toggle('hide', logged); $('app').classList.toggle('hide', !logged); }
async function boot(){
  const r = await api('/api/me');
  if(r.ok){ show(true); $('outPath').textContent = r.j.out; if(!r.j.ffmpeg) $('ffwarn').textContent = 'تنبيه: ffmpeg غير موجود في PATH؛ ملفات HLS لن تُدمج في mp4.'; }
  else show(false);
}
$('loginBtn').onclick = async()=>{
  const r = await api('/api/login',{u:$('lu').value.trim(),p:$('lp').value});
  if(r.ok) boot(); else $('loginErr').textContent = r.j.error||'خطأ';
};
$('lp').addEventListener('keydown',e=>{if(e.key==='Enter')$('loginBtn').click()});

async function runTask(kind, params, onTick){
  const r = await api('/api/task', Object.assign({kind}, params));
  if(!r.ok) throw new Error(r.j.error||'error');
  const id = r.j.id; let since = 0;
  for(;;){
    await new Promise(s=>setTimeout(s,900));
    const q = await api('/api/job?id='+id+'&since='+since);
    if(!q.ok) throw new Error(q.j.error||'lost');
    since = q.j.next;
    if(onTick) onTick(q.j);
    if(['done','error','cancelled'].includes(q.j.status)) return q.j;
  }
}

$('anBtn').onclick = async()=>{
  const url = $('url').value.trim(); if(!url) return;
  $('anBtn').disabled = true; $('anMsg').textContent = 'جارٍ تحليل الرابط ...';
  ['seasonCard','epCard','optCard','runCard'].forEach(i=>$(i).classList.add('hide'));
  try{
    const j = await runTask('analyze',{url});
    if(j.status!=='done'){ $('anMsg').textContent = 'تعذّر التحليل: '+(j.error||j.status); return; }
    A = j.result; items = []; sel.clear();
    $('o_prefix').value = A.title && A.kind!=='episode' ? A.title : '';
    if(A.kind==='series'){
      $('anMsg').textContent = 'مسلسل: '+A.title+' — '+A.seasons.length+' موسم';
      seasonsSel = new Set(A.selected? [A.selected] : A.seasons.map(s=>s.n));
      drawSeasons(); $('seasonCard').classList.remove('hide');
    } else if(A.kind==='list'){
      $('anMsg').textContent = 'صفحة قائمة: '+A.title+' — جارٍ جلب الفيديوهات ...';
      await loadEpisodes();
    } else {
      $('anMsg').textContent = 'فيديو واحد';
      items = [{href:url, label:'', sub:'', season:null, vid:A.vid||''}]; sel = new Set([0]);
      $('optCard').classList.remove('hide'); $('runInfo').textContent = '1 فيديو';
    }
  }catch(e){ $('anMsg').textContent = 'خطأ: '+e.message; }
  finally{ $('anBtn').disabled = false; }
};
function drawSeasons(){
  $('seasons').innerHTML = '';
  A.seasons.forEach(s=>{
    const d = document.createElement('div'); d.className = 'chip'+(seasonsSel.has(s.n)?' on':''); d.textContent = 'الموسم '+s.n;
    d.onclick = ()=>{ seasonsSel.has(s.n)?seasonsSel.delete(s.n):seasonsSel.add(s.n); drawSeasons(); };
    $('seasons').appendChild(d);
  });
}
$('allS').onclick = ()=>{ seasonsSel = new Set(A.seasons.map(s=>s.n)); drawSeasons(); };
$('noS').onclick = ()=>{ seasonsSel.clear(); drawSeasons(); };
$('loadEps').onclick = loadEpisodes;

async function loadEpisodes(){
  const body = {url:A.url};
  if(A.kind==='series'){
    const ss = A.seasons.filter(s=>seasonsSel.has(s.n));
    if(!ss.length){ $('anMsg').textContent = 'اختر موسما واحدا على الأقل'; return; }
    Object.assign(body,{stype:'series', seasons:ss});
  } else body.stype = 'list';
  $('loadEps').disabled = true; $('anMsg').textContent = 'جارٍ جلب قائمة الحلقات ...';
  try{
    const j = await runTask('episodes', body, q=>{ const l=q.log.filter(x=>/page \d+/.test(x)); if(l.length) $('anMsg').textContent = 'جارٍ جلب الحلقات: '+l[l.length-1].trim(); });
    if(j.status!=='done'){ $('anMsg').textContent = 'تعذّر جلب الحلقات: '+(j.error||j.status); return; }
    items = j.result.items; sel = new Set(items.map((_,i)=>i));
    $('anMsg').textContent = (A.title||'')+' — '+items.length+' فيديو';
    drawEps(); $('epCard').classList.remove('hide'); $('optCard').classList.remove('hide');
  }catch(e){ $('anMsg').textContent = 'خطأ: '+e.message; }
  finally{ $('loadEps').disabled = false; }
}
function epName(e){ return (e.season!=null && seasonsSel.size>1 ? 'م'+e.season+' · ' : '') + e.label; }
function drawEps(){
  const f = $('flt').value.trim().toLowerCase(); const box = $('eps'); box.innerHTML = '';
  items.forEach((e,i)=>{
    const name = epName(e); if(f && !name.toLowerCase().includes(f) && !(e.text||'').toLowerCase().includes(f)) return;
    const d = document.createElement('div'); d.className = 'ep'+(sel.has(i)?' on':''); d.textContent = name; d.title = e.text||'';
    d.onclick = ()=>{ sel.has(i)?sel.delete(i):sel.add(i); drawEps(); };
    box.appendChild(d);
  });
  $('epCount').textContent = '(المحدد '+sel.size+' من '+items.length+')'; $('runInfo').textContent = sel.size+' فيديو';
}
$('flt').oninput = drawEps;
$('allE').onclick = ()=>{ sel = new Set(items.map((_,i)=>i)); drawEps(); };
$('noE').onclick = ()=>{ sel.clear(); drawEps(); };
$('rngBtn').onclick = ()=>{
  const a = parseFloat($('rf').value), b = parseFloat($('rt').value); sel.clear();
  items.forEach((e,i)=>{ const n = e.num; if(n==null) return; if((isNaN(a)||n>=a)&&(isNaN(b)||n<=b)) sel.add(i); }); drawEps();
};

function opts(){
  return {mode:$('o_mode').value, quality:$('o_quality').value, parallel:+$('o_parallel').value||2, workers:+$('o_workers').value||16,
          minmin:$('o_minmin').value, preferred:$('o_pref').value, avoid:$('o_avoid').value, outer:$('o_outer').checked, retry:$('o_retry').checked};
}
let logSince = 0;
$('runBtn').onclick = async()=>{
  const chosen = items.map((e,i)=>[e,i]).filter(([e,i])=>sel.has(i)).map(([e])=>({href:e.href,label:e.label,sub:e.sub||'',season:e.season,vid:e.vid}));
  if(!chosen.length){ $('runInfo').textContent = 'لم تحدد شيئا'; return; }
  const r = await api('/api/task',{kind:'run', items:chosen, prefix:$('o_prefix').value, options:opts()});
  if(!r.ok){ $('runInfo').textContent = r.j.error||'خطأ'; return; }
  curJob = r.j.id; logSince = 0; $('log').textContent = ''; $('runCard').classList.remove('hide'); $('runBtn').disabled = true;
  $('runCard').scrollIntoView({behavior:'smooth'});
  if(poll) clearInterval(poll);
  poll = setInterval(tick, 1000); tick();
};
async function tick(){
  const q = await api('/api/job?id='+curJob+'&since='+logSince); if(!q.ok) return; const j = q.j;
  if(j.log.length){ const L = $('log'); const atEnd = L.scrollTop+L.clientHeight >= L.scrollHeight-20; L.textContent += j.log.join('\n')+'\n'; if(atEnd) L.scrollTop = L.scrollHeight; }
  logSince = j.next;
  const E = j.entries||[]; const tb = $('rows'); tb.innerHTML = '';
  let fin = 0;
  E.forEach((e,k)=>{
    if(['done','failed','skipped','cancelled'].includes(e.status)) fin++;
    const tr = document.createElement('tr');
    tr.innerHTML = '<td>'+(k+1)+'</td><td class="n"></td><td class="st '+e.status+'">'+(ST[e.status]||e.status)+'</td><td class="n"></td><td class="n"></td>';
    tr.children[1].textContent = (e.sub?e.sub+'/':'')+e.label; tr.children[3].textContent = e.server||''; tr.children[4].textContent = e.prog||'';
    tb.appendChild(tr);
  });
  $('bar').style.width = (E.length? Math.round(100*fin/E.length):0)+'%';
  const fin_ = ['done','error','cancelled'].includes(j.status);
  $('runStat').textContent = fin_ ? '— انتهى'+(j.result? ' ('+j.result.done+' نجح، '+j.result.failed+' فشل، '+j.result.skipped+' موجود)':'') : '— '+fin+'/'+E.length;
  if(fin_){ clearInterval(poll); poll = null; $('runBtn').disabled = false; if(j.error) $('runStat').textContent += ' — '+j.error; }
}
$('stopBtn').onclick = ()=>{ if(curJob) api('/api/cancel',{id:curJob}); };
$('openBtn').onclick = ()=>api('/api/open',{});
boot();
</script>
</body>
</html>
"""


# ================================================================= command line mode + entry point
def install():
    for cmd in ([sys.executable, "-m", "pip", "install", "--upgrade", "playwright", "requests"],
                [sys.executable, "-m", "playwright", "install", "chromium"]):
        print(">", " ".join(cmd), flush=True)
        subprocess.call(cmd)


def cli(urls):
    from playwright.sync_api import sync_playwright
    report = []
    with sync_playwright() as p:
        closer, ctx = new_context(p)
        try:
            for src in urls:
                a = analyze(ctx, src)
                if a["kind"] == "series":
                    sel = a.get("selected")
                    seasons = [s for s in a["seasons"] if (not SEASONS or s["n"] in SEASONS) and (sel is None or s["n"] == sel)]
                    items = []
                    for s in seasons:
                        items += list_items(ctx, s["url"], season=s["n"])
                    multi = len({e["season"] for e in items}) > 1
                    for e in items:
                        e["sub"] = f"S{e['season']}" if multi else ""
                elif a["kind"] == "list":
                    items = list_items(ctx, src)
                else:
                    items = [{"href": src, "label": "", "sub": "", "num": None}]
                items = [e for e in items if e.get("num") is None or ((EP_FROM is None or e["num"] >= EP_FROM) and (EP_TO is None or e["num"] <= EP_TO))]
                for e in items:
                    process(ctx, e["href"], e.get("label", ""), report, sub=e.get("sub", ""), prefix=safe_name(a["title"]) if a["kind"] != "episode" else "")
        finally:
            closer.close()
    ok = sum(1 for r in report if r["ok"])
    print(f"\ndone: {ok}/{len(report)} ok")
    with open("mmgrab_report.json", "w", encoding="utf-8") as f:
        json.dump(report, f, ensure_ascii=False, indent=1, default=str)


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    if args and args[0] == "install":
        return install()
    try:
        import playwright  # noqa: F401
    except ImportError:
        sys.exit("playwright is missing.  Run:   py mmgrab.py install")
    urls = [a for a in args if a.startswith("http")]
    fl = opt("file", "", str)
    if fl:
        urls += [x.strip() for x in open(fl, encoding="utf-8") if x.strip().startswith("http")]
    if urls:
        return cli(urls)
    studio(sys.argv[1:])


if __name__ == "__main__":
    main()
