import itertools


# $\mathcal{J}^v=\{A_{\Delta}\in\mathcal{J}:v\not\in\Delta\}$.
# Day & Wade (2020), p. 264
# J is a set of subsets of a graph, represented by a list of boolean arrays of equal length
# v is a vertex, represented by its index
def exclude(J: [[bool]], v: int):
    return [S for S in J if not S[v]]


# Whether $A\subseteq B$.
# A, B are subsets of the vertex set of the same graph, represented by boolean arrays of equal length
def subset_of(A: [bool], B: [bool]):
    assert(len(A) == len(B))
    for i in range(len(A)):
        if A[i] and not B[i]:
            return False
    return True


# Converts a boolean array representing a subset of the vertices of a graph
# to a dictionary mapping the positive indices into their position among the positive indices.
# Example: [False, True, False, True, True] -> {1: 0, 3: 1, 4: 2}
def mask_to_dict(S: [bool]):
    cnt = 0
    S_dict = {}
    for i in range(len(S)):
        if S[i]:
            S_dict[i] = cnt
            cnt += 1
    return S_dict


# $(\mathcal{G})_{\Delta}=\{A_{\Delta\cap\Theta}|A_{\Theta}\in\mathcal{G}\}-\{A_{\Delta}\}$
# Day & Wade (2020), p. 270
# G is a set of subsets of the vertex set of the same graph
# Delta is a subset of the vertex set representing an induced subgraph to that each set in G should be restricted to
def induced_invariant_subgraphs(G: [[bool]], Delta: [bool]):
    D_dict = mask_to_dict(Delta)
    G_Delta = []
    for Theta in G:
        assert(len(Theta) == len(Delta))
        DCapTheta = [False] * len(D_dict)
        for i in range(len(Delta)):
            if Theta[i] and Delta[i]:
                DCapTheta[D_dict[i]] = True
        G_Delta.append(tuple(DCapTheta))
    G_Delta_st = set(G_Delta)
    if tuple([True] * len(D_dict)) in G_Delta_st:
        G_Delta_st.remove(tuple([True] * len(D_dict)))
    return [list(S) for S in G_Delta_st]


def test1():
    # exclude
    assert(exclude([[True, False, True], [False, True, True], [False, False, True]], 1) == [[True, False, True], [False, False, True]])

    # subset_of
    assert(subset_of([], []))
    assert(subset_of([True, False], [True, False]))
    assert(subset_of([False, True, False], [True, True, False]))
    assert(not subset_of([True, True], [True, False]))

    # mask_to_dict
    d = mask_to_dict([False, True, True, False, True])
    assert(d[1] == 0 and d[2] == 1 and d[4] == 2 and len(d) == 3)

    # induced_invariant_subgraphs
    G_Delta = induced_invariant_subgraphs([[True, False, True, True, False], [True, False, False, True, True], [True, True, False, True, True], [False, True, True, False, True]], [True, True, False, True, False])
    assert([True, False, True] in G_Delta)
    assert([False, True, False] in G_Delta)
    assert(len(G_Delta) == 2)


# disjoint set union
class dsu:

    # N0 is the number of elements of the disjoint set union
    # Initially, each element forms a singleton set.
    def __init__(self, N0: int):
        self.N = N0
        self.a = [i for i in range(N0)]

    # Find the representative of element v where 0 <= v < self.N
    def find(self, v: int):
        assert(0 <= v < self.N)
        if self.a[v] == v:
            return v
        rep = self.find(self.a[v])
        self.a[v] = rep
        return rep

    # Merge the sets that contain u and v
    def union(self, u: int, v: int):
        self.a[self.find(v)] = self.find(u)


# Count the number of True's in msk
# msk is a boolean array
def count_true(msk: [bool]):
    cnt_true = 0
    for b in msk:
        if b:
            cnt_true += 1
    return cnt_true


def test2():
    # dsu
    ss = dsu(4)
    assert(ss.find(0) == 0 and ss.find(1) == 1 and ss.find(2) == 2 and ss.find(3) == 3)
    ss.union(0, 3)
    assert(ss.find(0) == ss.find(3) and ss.find(1) == 1 and ss.find(2) == 2)
    ss.union(0, 3)
    assert(ss.find(0) == ss.find(3) and ss.find(1) == 1 and ss.find(2) == 2)
    ss.union(2, 1)
    assert(ss.find(0) == ss.find(3) and ss.find(1) == ss.find(2))
    ss.union(2, 3)
    assert(ss.find(0) == ss.find(1) == ss.find(2) == ss.find(3))

    # count_true
    assert(count_true([]) == 0)
    assert(count_true([False, False]) == 0)
    assert(count_true([True, False, True, True, False]) == 3)


# An undirected graph without duplicate edges or loops, also seen as a right-angled Artin group
class graph:

    # N0 is the number of vertices
    # E0 is the adjacency table with type bool[0..N0][0..N0]
    def __init__(self, N0: int, E0: [[bool]]):
        self.N = N0
        self.E = E0

    # lk(v) = link(v) = {u\in V: (u, v)\in E}
    # v is an integer representing a vertex
    def link(self, v: int):
        assert(0 <= v < self.N)
        return self.E[v].copy()

    # st(v) = star(v) = link(v) \cup {v}
    # v is an integer representing a vertex
    def star(self, v: int):
        assert(0 <= v < self.N)
        adj_v = self.E[v].copy()
        adj_v[v] = True
        return adj_v

    # $v\leq_{(\mathcal{G},\mathcal{H})w$ iff lk(v)\subseteq st(w) and $v\not\in\mathcal{G}^w\cup\mathcal{H}$
    # Day & Wade (2020), p. 264
    # G, H are collections of vertex subsets
    # v, w are integers representing vertices
    def leq_GH(self, G: [[bool]], H: [[bool]], v: int, w: int):
        assert(0 <= v < self.N)
        assert(0 <= w < self.N)
        if not subset_of(self.link(v), self.star(w)):
            return False
        for S in exclude(G, w) + H:
            if S[v]:
                return False
        return True

    # $\Delta$ is upwards closed under $\leq_{(\mathcal{G},\mathcal{H})$
    # if $v\in\Delta$ and $v\leq_{(\mathcal{G},\mathcal{H})}w$ implies that $w\in\Delta$
    # Day & Wade (2020), p. 264
    # G, H are collections of vertex subsets
    # v, w are integers representing vertices
    def upwards_closed(self, G: [[bool]], H: [[bool]], Delta: [bool]):
        for v in range(self.N):
            if Delta[v]:
                for w in range(self.N):
                    if not Delta[w] and self.leq_GH(G, H, v, w):
                        return False
        return True

    # Returns a dsu representing the $(\mathcal{G}^v\cup\mathcal{H})$-components of A\st(v)
    # For a collection of vertex subsets C, the C-components of A\st(v) are the connected components of A\st(v)
    # such that for each S\in C, the connected components of the vertices v\in S within A\st(v) are merged.
    # G, H are collections of vertex subsets
    # v is an integer representing a vertex
    def GH_component_dsu(self, G: [[bool]], H: [[bool]], v: int):
        ident = exclude(G, v) + H
        cc = dsu(self.N)
        st_v = self.star(v)
        for i in range(self.N):
            if not st_v[i]:
                for j in range(self.N):
                    if not st_v[j] and self.E[i][j]:
                        cc.union(i, j)
        for S in ident:
            for i in range(self.N):
                if not st_v[i] and S[i]:
                    for j in range(i, self.N):
                        if not st_v[j] and S[j]:
                            cc.union(i, j)
                    break
        return cc

    # Returns the number of (\mathcal{G}^v\cup\mathcal{H})$-components of A\st(v).
    # G, H are collections of vertex subsets
    # v is an integer representing a vertex
    def num_GH_components(self, G: [[bool]], H: [[bool]], v: int):
        st_v = self.star(v)
        GHdsu = self.GH_component_dsu(G, H, v)
        GHcc = [False] * self.N
        for u in range(self.N):
            if not st_v[u]:
                GHcc[GHdsu.find(u)] = True
        return count_true(GHcc)

    # $\Delta$ is $(\mathcal{G},\mathcal{H})$-star-separated by a vertex v if
    # $\Delta$ intersects more than one $(\mathcal{G}^v\cup\mathcal{H})$-component of $\Gamma-\text{st}(v)$.
    # Day & Wade (2020), p. 264
    # G, H are collections of vertex subsets
    # v is an integer representing a vertex
    # Delta is a boolean array representing a vertex subset
    def GH_star_separated(self, G: [[bool]], H: [[bool]], v: int, Delta: [bool]):
        st_v = self.star(v)
        cc = self.GH_component_dsu(G, H, v)
        for i in range(self.N):
            if not st_v[i] and Delta[i]:
                for j in range(i + 1, self.N):
                    if not st_v[j] and Delta[j] and cc.find(j) != cc.find(i):
                        return True
                return False
        return False

    # $A_{\Delta}$ is invariant under $\text{Out}^0(A_{\Gamma};\mathcal{G},\mathcal{H}^t)$ iff
    # $\Delta$ is upwards-closed under $\leq_{(\mathcal{G},\mathcal{H})} and
    # $\Delta$ is not $(\mathcal{G},\mathcal{H})$-star-separated by a vertex $v\in\Gamma-\Delta$.
    # Day & Wade (2020), p. 265
    # G, H are collections of vertex subsets
    # Delta is a boolean array representing a vertex subset
    def preserved_by(self, G: [[bool]], H: [[bool]], Delta: [bool]):
        if not self.upwards_closed(G, H, Delta):
            return False
        for v in range(self.N):
            if not Delta[v] and self.GH_star_separated(G, H, v, Delta):
                return False
        return True

    # The saturation $\mathcal{G}'$ relative to $(\mathcal{G},\mathcal{H})$
    # is the collection of all induced subgroups preserved by $\text{Out}^0(\Gamma;\mathcal{G},\mathcal{H}^t)$.
    # We have excluded the trivial induced subgroups {1} and the whole of A here
    # to avoid extra testing of non-triviality later.
    # Day & Wade (2020), p. 270
    # G, H are collections of vertex subsets
    def saturate(self, G: [[bool]], H: [[bool]]):
        subset_lst = [[False, True] for _ in range(self.N)]
        return [list(S) for S in itertools.product(*subset_lst) if 0 < count_true(list(S)) < self.N and self.preserved_by(G, H, S)]

    # Returns whether $\text{Out}^0(A_{\Gamma};\mathcal{G},\mathcal{H}^t)$ is trivial.
    # Only applies to the case where the above is the image of a restriction homomorphism
    # because in this case we can simply test whether there exist generators preserving G and fixing H
    # (and thus lying in $\text{Out}^0(A_{\Gamma};\mathcal{G},\mathcal{H}^t)$).
    # Day & Wade (2020), p. 270
    # G, H are collections of vertex subsets
    def Out0_non_trivial(self, G: [[bool]], H: [[bool]]):
        # inversions
        # The inversion $[\eta_v]$ fixes S iff $v\not\in S$. It always preserves S.
        # Day & Wade (2020), p. 264
        for v in range(self.N):
            in_Out0 = True
            for S in H:
                if S[v]:
                    in_Out0 = False
                    break
            if in_Out0:
                return True

        # transvections
        # The transvection $[\rho_v^w]$ fixes S iff $v\not\in S$. It preserves S iff $v\not\in S$ or $v,w\in S$.
        # Day & Wade (2020), p. 264
        # The following code is commented out because
        # if $[\rho_v^w]\in\text{Out}^0(A_{\Gamma};\mathcal{G},\mathcal{H}^t)$,
        # then $[\eta_v]\in\text{Out}^0(A_{\Gamma};\mathcal{G},\mathcal{H}^t)$.

        # for w in range(self.N):
        #     ident = exclude(G, w) + H
        #     for v in range(self.N):
        #         in_Out0 = True
        #         for S in ident:
        #             if S[v]:
        #                 in_Out0 = False
        #                 break
        #         if in_Out0:
        #             return True

        # extended partial conjugations
        # $[\pi_K^v]$ is non-trivial iff K is neither empty nor the whole of A\st(v).
        # $[\pi_K^v]$ fixes S iff $K\cap S\neq\emptyset\Rightarrow S\backslash st(v)\subseteq K$. (*)
        # It preserves S iff (*) or $v\in S$.
        # Day & Wade (2020), p. 264
        for v in range(self.N):
            cc = self.GH_component_dsu([], [], v)
            st_v = self.star(v)
            cc_map = {}
            for i in range(self.N):
                if not st_v[i]:
                    if cc.find(i) not in cc_map:
                        cc_map[cc.find(i)] = []
                    cc_map[cc.find(i)].append(i)
            cc_lst = list(cc_map.items())
            subset_lst = [[False, True] for _ in range(len(cc_lst))]
            ident = exclude(G, v) + H
            for K_msk_ in itertools.product(*subset_lst):
                K_msk = list(K_msk_)
                if count_true(K_msk) == 0 or count_true(K_msk) == len(cc_lst):
                    continue
                K = [False] * self.N
                for i in range(len(cc_lst)):
                    if K_msk[i]:
                        for u in cc_lst[i][1]:
                            K[u] = True
                in_Out0 = True
                for S in ident:
                    for u in range(self.N):
                        if K[u] and S[u]:
                            # $K\cap S\neq\emptyset\Rightarrow S\backslash\text{st}(v)\subseteq K$
                            for w in range(self.N):
                                if S[w] and not st_v[w] and not K[w]:
                                    in_Out0 = False
                                    break
                            break
                    if not in_Out0:
                        break
                if in_Out0:
                    return True
        return False

    # Returns the subgraph induced by $S\subseteq V(\Gamma)$, respecting the ordering of the vertices.
    # S is a boolean array representing a vertex subset.
    def induced_subgraph(self, S: [bool]):
        S_dict = mask_to_dict(S)
        N0 = len(S_dict)
        E0 = [[False] * N0 for _ in range(N0)]
        for u in range(self.N):
            if S[u]:
                for v in range(self.N):
                    if S[v] and self.E[u][v]:
                        E0[S_dict[u]][S_dict[v]] = True
        return graph(N0, E0)

    # Returns whether the graph is connected.
    def connected(self):
        if self.N == 0:
            return True
        cc = dsu(self.N)
        for u in range(self.N):
            for v in range(u + 1, self.N):
                if self.E[u][v]:
                    cc.union(u, v)
        for u in range(self.N):
            if cc.find(u) != cc.find(0):
                return False
        return True

    # Returns the number of edges in the graph, used in tests to ensure that the enumerated edge set is the whole set.
    def num_edges(self):
        Ne = 0
        for u in range(self.N):
            for v in range(u + 1, self.N):
                if self.E[u][v]:
                    Ne += 1
        return Ne


# Constructs an undirected graph from the number of vertices and the set of edges.
# N is an integer representing the number of vertices.
# E is a list of pairs of integers representing the endpoints of each edge.
def graph_from_edges(N: int, UV: [(int, int)]):
    E = [[False] * N for _ in range(N)]
    for u, v in UV:
        E[u][v] = E[v][u] = True
    return graph(N, E)


def test3():
    A = graph_from_edges(5, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (2, 3)])

    # link, star
    assert(A.link(1) == [True, False, True, False, True])
    assert(A.star(3) == [True, False, True, True, False])

    # leq_GH
    assert(A.leq_GH([], [], 0, 2) and A.leq_GH([], [], 2, 0))
    assert(A.leq_GH([], [], 3, 1) and A.leq_GH([], [], 3, 0))
    assert(A.leq_GH([], [], 4, 1) and A.leq_GH([], [], 4, 2))
    assert(not A.leq_GH([], [], 3, 4) and not A.leq_GH([], [], 4, 3))
    assert(not A.leq_GH([], [], 1, 0) and not A.leq_GH([], [], 2, 1))
    assert(not A.leq_GH([], [], 1, 4) and not A.leq_GH([], [], 2, 3))
    assert(A.leq_GH([[True, False, False, True, False]], [], 3, 0))
    assert(not A.leq_GH([[True, False, False, True, False]], [], 3, 2))
    assert(not A.leq_GH([], [[True, False, False, True, False]], 3, 0))
    assert(A.leq_GH([], [[True, False, False, False, True]], 3, 0))

    # upwards_closed
    assert(A.upwards_closed([], [], [True, False, True, False, False]))
    assert(A.upwards_closed([], [], [True, True, True, False, False]))
    assert(A.upwards_closed([], [], [True, True, True, False, True]))
    assert(not A.upwards_closed([], [], [True, False, True, False, True]))
    assert(A.upwards_closed([[True, False, True, False, True]], [], [True, False, True, False, True]))
    assert(not A.upwards_closed([[True, False, True, False, True]], [], [True, False, False, False, True]))

    # preserved_by
    assert(A.preserved_by([], [], [True, True, True, True, False]))
    assert(not A.preserved_by([], [], [True, True, False, False, False]))
    assert(A.preserved_by([], [], [True, False, True, False, False]))

    # Out0_non_trivial
    assert(A.Out0_non_trivial([], [[True, True, True, True, False]]))
    A = graph_from_edges(4, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)])
    assert(not A.Out0_non_trivial([], [[True, True, True, True, True]]))

    A = graph_from_edges(9, [(0, 1), (0, 2), (1, 2), (1, 6), (3, 4), (3, 8), (4, 6), (5, 8), (6, 7), (7, 8)])

    # GH_component_dsu, num_GH_components, GH_star_separated
    cc = A.GH_component_dsu([], [], 7)
    assert(cc.find(0) == cc.find(1) == cc.find(2) and cc.find(3) == cc.find(4))
    assert(A.num_GH_components([], [], 7) == 3)
    assert(not A.GH_star_separated([], [], 7, [True, True, True, False, False, False, False, False, False]))
    assert(A.GH_star_separated([], [], 7, [True, True, True, False, False, True, False, False, False]))

    args2 = [[], [[False, True, False, False, True, True, False, False, False]], 7]
    cc = A.GH_component_dsu(*args2)
    assert(cc.find(0) == cc.find(1) == cc.find(2) == cc.find(3) == cc.find(4) == cc.find(5))
    assert(A.num_GH_components(*args2) == 1)
    assert(not A.GH_star_separated(*args2, [True] * 9))

    args3 = [[], [[False, False, False, False, True, True, False, False, False]], 7]
    cc = A.GH_component_dsu(*args3)
    assert(cc.find(0) == cc.find(1) == cc.find(2) and cc.find(3) == cc.find(4) == cc.find(5))
    assert(A.num_GH_components(*args3) == 2)
    assert(A.GH_star_separated(*args3, [False, True, False, False, False, True, False, False, False]))
    assert(not A.GH_star_separated(*args3, [True, True, True, False, False, False, True, True, True]))

    cc = A.GH_component_dsu([[False, False, True, False, False, True, False, True, False]], [[False, False, False, False, True, True, False, False, False]], 7)
    assert(cc.find(0) == cc.find(1) == cc.find(2) and cc.find(3) == cc.find(4) == cc.find(5))
    assert(cc.find(0) != cc.find(3))

    # preserved_by
    A = graph_from_edges(10, [(0, 1), (0, 2), (0, 4), (1, 3), (2, 3), (4, 5), (3, 6), (6, 7), (5, 8), (8, 9)])
    assert(not A.preserved_by([], [], [False, False, False, True, False, True, True, True, True, True]))

    # induced_subgraph
    A = graph_from_edges(4, [(0, 2), (1, 2), (3, 2)]).induced_subgraph([True, True, False, True])
    assert(A.N == 3 and A.num_edges() == 0)
    A = graph_from_edges(6, [(0, 2), (0, 5), (1, 4), (1, 5), (2, 3), (2, 4), (2, 5), (3, 5)]).induced_subgraph([True, False, True, False, True, True])
    assert(A.E[0][1] and A.E[0][3] and A.E[1][2] and A.E[1][3] and A.num_edges() == 4)

    # connected
    assert(not graph_from_edges(4, [(0, 2), (1, 3)]).connected())
    assert(graph_from_edges(4, [(0, 2), (3, 2), (1, 3)]).connected())


# Returns the maximum (not just maximal) size of any clique of the graph $\Delta$.
# Dynamic programming approach, time complexity O(2^nn^2).
# Generally a NP-complete problem.
def maximal_clique(Delta: graph):
    is_clique = [False] * (2 ** Delta.N)
    is_clique[0] = True
    max_clique = 0
    for msk in range(2 ** Delta.N):
        if is_clique[msk]:
            if msk.bit_count() > max_clique:
                max_clique = msk.bit_count()
            for v in range(Delta.N):
                if (msk >> v) & 1 == 0:
                    feasible = True
                    for u in range(Delta.N):
                        if (msk >> u) & 1 == 1 and not Delta.E[u][v]:
                            feasible = False
                            break
                    if feasible:
                        is_clique[msk | (1 << v)] = True
    return max_clique


# Returns the center of $A_{\Delta}$, represented by an induced subgraph generating the center.
def center(Delta: graph):
    return [Delta.E[u] == [True] * u + [False] + [True] * (Delta.N - u - 1) for u in range(Delta.N)]


# Returns the rank of the center of $A_{\Delta}$ (viewed as a free Abelian group).
def rank_of_center(Delta: graph):
    cnt = 0
    for u in range(Delta.N):
        if Delta.E[u] == [True] * u + [False] + [True] * (Delta.N - u - 1):
            cnt += 1
    return cnt


def test4():
    # maximal_clique
    assert(maximal_clique(graph_from_edges(5, [])) == 1)
    assert(maximal_clique(graph_from_edges(4, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)])) == 4)
    assert(maximal_clique(graph_from_edges(4, [(0, 1), (0, 2), (1, 2), (1, 3), (2, 3)])) == 3)
    assert(maximal_clique(graph_from_edges(6, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3), (1, 4), (2, 4), (3, 5)])) == 4)
    assert(maximal_clique(graph_from_edges(6, [(0, 1), (0, 2), (1, 2), (3, 4)])) == 3)

    # center, rank_of_center
    E = [[False] * 6 for _ in range(6)]
    for u in range(6):
        for v in range(u + 1, 6):
            if (u, v) not in [(0, 3), (0, 4), (2, 4)]:
                E[u][v] = E[v][u] = True
    A = graph(6, E)
    assert(center(A) == [False, True, False, False, False, True])
    assert(rank_of_center(A) == 2)

    A = graph_from_edges(1, [])
    assert(center(A) == [True] and rank_of_center(A) == 1)

    A = graph_from_edges(2, [(0, 1)])
    assert(center(A) == [True, True] and rank_of_center(A) == 2)


# Returns the vcd of a Fouxe-Rabinovitch group associated to a free factor decomposition
# $A_{\Delta}=A_{\Delta_1} * \cdots * A_{\Delta_k} * F_m$.
# k = 0, m <= 1 follows from computation
# k = 0, m > 1 follows from Culler & Vogtmann (1986)
# k > 0 follows from Day & Wade (2020), p. 268
# Delta = [Delta_1, ..., Delta_k] is a list of graphs
# m is an integer representing the free rank
def vcd_Fouxe_Rabinovitch(Delta: [graph], m: int):
    k = len(Delta)
    if k == 0:
        if m <= 1:
            # Out(0) = Aut(0) = 0; vcd(0) = 0
            # Out(Z) = Aut(Z) = Z/2Z; vcd(Z/2Z) = 0
            return 0
        # Moduli of graphs and automorphisms of free groups, Culler & Vogtmann (1986)
        return 2 * m - 3
    # Day & Wade (2020), p. 268
    vcd = 0
    max_clique = 0
    for Delta_i in Delta:
        d_Delta_i = maximal_clique(Delta_i)
        z_Delta_i = rank_of_center(Delta_i)
        if d_Delta_i > max_clique:
            max_clique = d_Delta_i
        vcd += d_Delta_i - z_Delta_i
    vcd += (k + 2 * m - 2) * max_clique
    return vcd


# Calculates vcd(Out(A;\mathcal{G},\mathcal{H}^t)).
# Day & Wade (2020), pp. 269-272
# A is a graph representing a right-angled Artin group
# G_, H are collections of vertex subsets
def virtual_cohomological_dimension(A: graph, G_: [[bool]], H: [[bool]]):
    # First, extend $\mathcal{G}$ to its saturation $\mathcal{G}'$ relative to $(\mathcal{G},\mathcal{H})$.
    # Day & Wade (2020), p. 270
    G = A.saturate(G_, H)
    # Is there a restriction map R_{\Delta} with non-trivial image?
    # The restriction homomorphism only makes sense when $\Delta\in\mathcal{G}$.
    # Day & Wade (2019), p. 761
    for Delta in G:
        # If $\Delta$ is a subset of some $S\in\mathcal{H}$, then the image of the restriction homomorphism is trivial.
        # In this case, the characterization of the image as a RORG does not apply, so we have to specifically test it.
        subset_of_H = False
        for S in H:
            if subset_of(Delta, S):
                subset_of_H = True
                break
        # If the image of the restriction homomorphism is not trivial,
        # return the sum of the vcd's of the descendants in the tree.
        # Day & Wade (2020), p. 270
        if not subset_of_H and A.induced_subgraph(Delta).Out0_non_trivial(induced_invariant_subgraphs(G, Delta), induced_invariant_subgraphs(H, Delta)):
            return virtual_cohomological_dimension(A, G, H + [Delta]) + virtual_cohomological_dimension(A.induced_subgraph(Delta), induced_invariant_subgraphs(G, Delta), induced_invariant_subgraphs(H, Delta))
    if not A.connected():
        # Cases 2a and 2b: A is disconnected.
        Gcc = dsu(A.N)
        for u in range(A.N):
            for v in range(A.N):
                if A.E[u][v]:
                    Gcc.union(u, v)
        # A graph is G-connected if its connected components are merged into one
        # by merging, for each S\in G, all components containing some vertex of S.
        for S in G:
            for u in range(A.N):
                if S[u]:
                    for v in range(A.N):
                        if S[v]:
                            Gcc.union(u, v)
                    break
        G_connected = True
        if A.N > 0:
            for u in range(A.N):
                if Gcc.find(u) != Gcc.find(0):
                    G_connected = False
        if not G_connected:
            # Case 2a: $\Gamma$ is disconnected and G-disconnected.
            in_G = [False] * A.N
            for S in G:
                for u in range(A.N):
                    if S[u]:
                        in_G[u] = True
            Delta = []
            m = 0
            ccs = [[] for _ in range(A.N)]
            for u in range(A.N):
                ccs[Gcc.find(u)] += [u]
            for u in range(A.N):
                if len(ccs[u]) > 0:
                    # A non-empty G-connected component
                    if len(ccs[u]) > 1 or in_G[ccs[u][0]]:
                        # The remaining G-connected components
                        # Day & Wade (2020), p. 270
                        Delta_i = [False] * A.N
                        for v in ccs[u]:
                            Delta_i[v] = True
                        Delta.append(A.induced_subgraph(Delta_i))
                    else:
                        # An isolated vertex not contained in any S\in G
                        # Day & Wade (2020), p. 270
                        m += 1
            return vcd_Fouxe_Rabinovitch(Delta, m)
        else:
            # Case 2b: $\Gamma$ is disconnected and G-connected.
            # The vertices v which $(\mathcal{G},\mathcal{H})$ separate form a complete graph $\Theta$.
            # A vertex v $(\mathcal{G},\mathcal{H})$ separates
            # if A\st(v) has more than one $(\mathcal{G}^v\cup\mathcal{H})$-component.
            siz_Theta = 0
            for v in range(A.N):
                if A.num_GH_components(G, H, v) > 1:
                    siz_Theta += 1
            return siz_Theta
    else:
        # Cases 2c, 2d and 2e: A is connected.
        # We are assuming that G=H at this point.
        rk_center = rank_of_center(A)
        if rk_center == 0:
            # Case 2c: The center of $A_{\Gamma}$ is trivial.
            # Day & Wade (2020), p. 270
            free_rank = 0
            for v in range(A.N):
                # N_v is the number of $(\mathcal{G},\mathcal{H})$-connected components of A\st(v).
                free_rank += A.num_GH_components(G, H, v) - 1
            return free_rank
        elif rk_center != A.N:
            # Case 2d: The center of $A_{\Gamma}$ is a proper, non-trivial subgroup.
            # Day & Wade (2020), p. 270
            Delta = [not b for b in center(A)]
            # $[\rho_w^{v'}]$ is a leaf transvection when $v'\in Z(A)$, $w\in\Delta$ and $w\leq_{\mathcal{G}}v'$.
            # Day & Wade (2019), p. 783
            num_leaf_transvections = 0
            for w in range(A.N):
                if Delta[w]:
                    for v in range(A.N):
                        if not Delta[v] and A.leq_GH(G, H, w, v):
                            num_leaf_transvections += 1
            return num_leaf_transvections + virtual_cohomological_dimension(A.induced_subgraph(Delta), induced_invariant_subgraphs(G, Delta), induced_invariant_subgraphs(H, Delta))
        else:
            # Case 2e: The center of $A_{\Gamma}$ is the whole of $\Gamma$.
            # Day & Wade (2020), p. 270
            # m is the number of elements of $\Gamma$ not contained in any element of $\mathcal{G}$.
            # The kernel of the projection map is a free Abelian group of rank m(n-m) and thus has vcd m(n-m).
            # The image of the projection map is GL(m,Z) with vcd m(m-1)/2.
            # Day & Wade (2019), p. 784
            m = 0
            in_G = [False] * A.N
            for S in G:
                for u in range(A.N):
                    if S[u]:
                        in_G[u] = True
            for u in range(A.N):
                if not in_G[u]:
                    m += 1
            return m * (A.N - m) + m * (m - 1) // 2


# Calculates the vcd of the untwisted outer automorphism group $U(A_{\Gamma})$
# which equals vcd(Out(A_{\Gamma};\mathcal{G}_{\geq}^{NA})).
# Day & Wade (2019), p. 789
def vcd_untwisted_Out(A: graph):
    G = []
    for v in range(A.N):
        S = [A.leq_GH([], [], v, w) and not A.E[v][w] for w in range(A.N)]
        if S != [True] * A.N:
            G.append(S)
    return virtual_cohomological_dimension(A, G, [])


# Generates a string of n diamonds, used for tests.
# Day & Wade (2019), p. 792
def string_of_diamonds(n: int):
    E = []
    for i in range(n):
        E += [(3*i, 3*i + 1), (3*i, 3*i + 2), (3*i + 1, 3*i + 3), (3*i + 2, 3*i + 3)]
    return graph_from_edges(3*n + 1, E)


# Generates a tree with one interior edge, n leaves on the left and m leaves on the right, used for tests.
# Charney, Crisp & Vogtmann (2007), p. 2258
def n11m_tree(n: int, m: int):
    return graph_from_edges(n + m + 2, [(i, n) for i in range(n)] + [(n, n + 1)] + [(n + 1, i) for i in range(n + 2, n + m + 2)])


# Generates the "butterfly" graph
# Charney, Stambaugh & Vogtmann (2017), p. 1158
def butterfly(n: int):
    return graph_from_edges(n + n + 3, [(0, i) for i in range(1, n + 1)] + [(i, n + 1) for i in range(1, n + 1)] + [(n + 1, i) for i in range(n + 2, n + n + 2)] + [(i, n + n + 2) for i in range(n + 2, n + n + 2)])


def test5():
    # vcd_Fouxe_Rabinovitch
    A1 = graph_from_edges(4, [(0, 1), (0, 2), (0, 3), (1, 2), (2, 3)])
    assert(vcd_Fouxe_Rabinovitch([A1], 1) == 4)
    assert(vcd_Fouxe_Rabinovitch([A1], 2) == 10)
    A2 = graph_from_edges(6, [(0, 1), (0, 2), (0, 3), (1, 2), (2, 3), (4, 5)])
    assert(vcd_Fouxe_Rabinovitch([A2], 1) == 6)
    assert(vcd_Fouxe_Rabinovitch([A2], 2) == 12)
    A3 = graph_from_edges(2, [(0, 1)])
    assert(vcd_Fouxe_Rabinovitch([A1, A3], 1) == 7)
    assert(vcd_Fouxe_Rabinovitch([A1, A3], 2) == 13)

    # virtual_cohomological_dimension
    # Out(F_m) = 2m - 3
    assert(virtual_cohomological_dimension(graph_from_edges(2, []), [], []) == 1)
    assert(virtual_cohomological_dimension(graph_from_edges(3, []), [], []) == 3)
    assert(virtual_cohomological_dimension(graph_from_edges(4, []), [], []) == 5)
    assert(virtual_cohomological_dimension(graph_from_edges(5, []), [], []) == 7)

    # Out(Z_n) = n * (n-1) / 2
    assert(virtual_cohomological_dimension(graph_from_edges(2, [(0, 1)]), [], []) == 1)
    assert(virtual_cohomological_dimension(graph_from_edges(3, [(0, 1), (0, 2), (1, 2)]), [], []) == 3)
    assert(virtual_cohomological_dimension(graph_from_edges(4, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]), [], []) == 6)

    # String of diamonds
    assert(virtual_cohomological_dimension(string_of_diamonds(1), [], []) == 2)
    assert(virtual_cohomological_dimension(string_of_diamonds(1), [[False, False, False, True]], []) == 2)
    assert(virtual_cohomological_dimension(string_of_diamonds(1), [], [[False, False, False, True]]) == 2)
    assert(virtual_cohomological_dimension(string_of_diamonds(1), [[True, False, False, False]], [[False, False, False, True]]) == 1)
    assert(virtual_cohomological_dimension(string_of_diamonds(2), [], []) == 7)
    assert(virtual_cohomological_dimension(string_of_diamonds(2), [], [[False] * 6 + [True]]) == 6)

    # n - 1 - 1 - m tree
    # Example 7.6, Automorphisms of 2–dimensional right-angled Artin groups, Geometry & Topology 11 (2007) p. 2258
    for n in range(1, 5):
        for m in range(n, 5):
            assert(virtual_cohomological_dimension(n11m_tree(n, m), [], []) == 3 * (n + m) - 2)

    # General tree
    # Outer space for untwisted automorphisms of right-angled Artin groups, Geometry & Topology 21 (2017) p. 1155
    assert(virtual_cohomological_dimension(graph_from_edges(3, [(0, 1), (1, 2)]), [], []) == 3)
    assert(virtual_cohomological_dimension(graph_from_edges(4, [(0, 1), (0, 2), (0, 3)]), [], []) == 6)
    assert(virtual_cohomological_dimension(graph_from_edges(5, [(0, 1), (0, 2), (1, 3), (1, 4)]), [], []) == 7)

    # Butterflies
    for n in range(2, 4):
        assert(virtual_cohomological_dimension(butterfly(n), [], []) == 4 * n - 1)

    assert(virtual_cohomological_dimension(graph_from_edges(4, [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]), [[True, True, False, False]], []) == 6)


# The root testing function.
def test():
    test1()
    test2()
    test3()
    test4()
    test5()


# test()
b = int(input('Index begins at? (0/1):'))
N = int(input('# of vertices:'))
M = int(input('# of edges:'))
E = [[False] * N for _ in range(N)]
for i in range(M):
    u = int(input('1st endpoint of edge ' + str(i + b) + ':'))
    v = int(input('2nd endpoint of edge ' + str(i + b) + ':'))
    u -= b
    v -= b
    E[u][v] = E[v][u] = True
A = graph(N, E)

if input('Calculate the vcd of the untwisted outer automorphism group? (y/N):') == 'y':
    print('vcd(U^0(A)) = ' + str(vcd_untwisted_Out(A)))
    exit(0)

NG = int(input('# of preserved induced subgroups:'))
G = [[False] * N for _ in range(NG)]
for i in range(NG):
    NGi = int(input('# of vertices in preserved induced subgroup ' + str(i + b) + ':'))
    for j in range(NGi):
        u = int(input('Vertex ' + str(j + b) + ' in preserved induced subgroup ' + str(i + b) + ':'))
        G[i][u - b] = True

NH = int(input('# of fixed induced subgroups:'))
H = [[False] * N for _ in range(NH)]
for i in range(NH):
    NHi = int(input('# of vertices in fixed induced subgroup ' + str(i + b) + ':'))
    for j in range(NHi):
        u = int(input('Vertex ' + str(j + b) + ' in fixed induced subgroup ' + str(i + b) + ':'))
        H[i][u - b] = True

print('vcd(Out(A, G, H^t)) = ' + str(virtual_cohomological_dimension(A, G, H)))
