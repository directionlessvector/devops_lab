#include <bits/stdc++.h>
using namespace std;

// ======================================================
// Fast IO
// ======================================================
#define fast ios::sync_with_stdio(false); cin.tie(nullptr);

// ======================================================
// Type Shortcuts
// ======================================================
#define ll long long
#define ull unsigned long long
#define ld long double

#define vi vector<int>
#define vll vector<ll>
#define pii pair<int,int>
#define pll pair<ll,ll>

// ======================================================
// STL Shortcuts
// ======================================================
#define pb push_back
#define eb emplace_back
#define mp make_pair
#define ff first
#define ss second

#define all(x) (x).begin(), (x).end()
#define rall(x) (x).rbegin(), (x).rend()
#define sz(x) (int)(x).size()

// ======================================================
// Loop Macros
// ======================================================
#define rep(i,a,b) for(int i = (a); i < (b); i++)
#define rrep(i,a,b) for(int i = (a); i >= (b); i--)
#define each(x,v) for(auto &x : v)

// ======================================================
// Constants
// ======================================================
const ll INF = 1e18;
const int MOD = 1e9 + 7;

// ======================================================
// Output Helpers
// ======================================================
void yes() { cout << "YES\n"; }
void no()  { cout << "NO\n"; }
void alice() { cout << "Alice\n"; }
void bob() { cout << "Bob\n"; }

template<typename T>
void input(vector<T> &a) {
    each(x, a) cin >> x;
}

template<typename T>
void show(const vector<T> &a) {
    each(x, a) cout << x << " ";
    cout << "\n";
}

// ======================================================
// Math Utilities
// ======================================================
ll gcd(ll a, ll b) {
    return (b == 0 ? a : gcd(b, a % b));
}

ll lcm(ll a, ll b) {
    return (a / gcd(a,b)) * b;
}

ll power(ll a, ll b, ll mod = MOD) {
    ll res = 1;
    while(b) {
        if(b & 1) res = (res * a) % mod;
        a = (a * a) % mod;
        b >>= 1;
    }
    return res;
}

// ======================================================
// Sieve of Eratosthenes
// ======================================================
struct Sieve {
    int n;
    vector<bool> is_prime;
    vector<int> primes;

    Sieve(int size) {
        n = size;
        is_prime.assign(n+1, true);
        is_prime[0] = is_prime[1] = false;

        for(int i = 2; i * i <= n; i++) {
            if(is_prime[i]) {
                for(int j = i*i; j <= n; j += i)
                    is_prime[j] = false;
            }
        }

        for(int i = 2; i <= n; i++)
            if(is_prime[i]) primes.pb(i);
    }
};

// ======================================================
// DSU (Disjoint Set Union)
// ======================================================
struct DSU {
    vector<int> parent, size;

    DSU(int n) {
        parent.resize(n);
        size.assign(n, 1);
        iota(all(parent), 0);
    }

    int find(int x) {
        if(parent[x] == x) return x;
        return parent[x] = find(parent[x]);
    }

    void unite(int a, int b) {
        a = find(a);
        b = find(b);
        if(a != b) {
            if(size[a] < size[b]) swap(a, b);
            parent[b] = a;
            size[a] += size[b];
        }
    }
};

// ======================================================
// Segment Tree (Range Sum)
// ======================================================
struct SegTree {
    int n;
    vector<ll> tree;

    SegTree(int size) {
        n = size;
        tree.assign(4*n, 0);
    }

    void build(vector<ll> &a, int id, int l, int r) {
        if(l == r) {
            tree[id] = a[l];
            return;
        }
        int mid = (l + r) / 2;
        build(a, 2*id, l, mid);
        build(a, 2*id+1, mid+1, r);
        tree[id] = tree[2*id] + tree[2*id+1];
    }

    void update(int id, int l, int r, int pos, ll val) {
        if(l == r) {
            tree[id] = val;
            return;
        }
        int mid = (l + r) / 2;
        if(pos <= mid) update(2*id, l, mid, pos, val);
        else update(2*id+1, mid+1, r, pos, val);
        tree[id] = tree[2*id] + tree[2*id+1];
    }

    ll query(int id, int l, int r, int ql, int qr) {
        if(qr < l || ql > r) return 0;
        if(ql <= l && r <= qr) return tree[id];
        int mid = (l + r) / 2;
        return query(2*id, l, mid, ql, qr)
             + query(2*id+1, mid+1, r, ql, qr);
    }
};

// ======================================================
// Graph Template (Adj List + BFS + DFS + Dijkstra)
// ======================================================

struct Graph {
    int n;
    vector<vector<pair<int,ll>>> adj; // {node, weight}

    Graph(int nodes) {
        n = nodes;
        adj.resize(n);
    }

    // For weighted graph
    void addEdge(int u, int v, ll w = 1, bool undirected = true) {
        adj[u].pb({v, w});
        if(undirected)
            adj[v].pb({u, w});
    }

    // ================= BFS =================
    vector<int> bfs(int src) {
        vector<int> dist(n, -1);
        queue<int> q;

        dist[src] = 0;
        q.push(src);

        while(!q.empty()) {
            int u = q.front(); q.pop();

            for(auto [v, w] : adj[u]) {
                if(dist[v] == -1) {
                    dist[v] = dist[u] + 1;
                    q.push(v);
                }
            }
        }

        return dist;
    }

    // ================= DFS =================
    void dfsUtil(int u, vector<bool> &vis) {
        vis[u] = true;
        for(auto [v, w] : adj[u]) {
            if(!vis[v])
                dfsUtil(v, vis);
        }
    }

    void dfs(int src) {
        vector<bool> vis(n, false);
        dfsUtil(src, vis);
    }

    // ================= Dijkstra =================
    vector<ll> dijkstra(int src) {
        vector<ll> dist(n, INF);
        priority_queue<pair<ll,int>, 
                       vector<pair<ll,int>>, 
                       greater<pair<ll,int>>> pq;

        dist[src] = 0;
        pq.push({0, src});

        while(!pq.empty()) {
            auto [d, u] = pq.top(); 
            pq.pop();

            if(d > dist[u]) continue;

            for(auto [v, w] : adj[u]) {
                if(dist[v] > dist[u] + w) {
                    dist[v] = dist[u] + w;
                    pq.push({dist[v], v});
                }
            }
        }

        return dist;
    }
};

// ======================================================
// PBDS (Ordered Set)
// ======================================================
#include <ext/pb_ds/assoc_container.hpp>
using namespace __gnu_pbds;

template<typename T>
using ordered_set = tree<
    T,
    null_type,
    less<T>,
    rb_tree_tag,
    tree_order_statistics_node_update>;

// ======================================================
// Solve Function
// ======================================================
void solve() {

    // Write problem logic here
    cout << "Hello World";
}

// ======================================================
// Main
// ======================================================
int main() {
    fast;

    int t = 1;
    cin >> t;
    while(t--) {
        solve();
    }

    return 0;
}