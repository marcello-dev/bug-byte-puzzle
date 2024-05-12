from collections import deque
import networkx as nx
import string
import time


class Node:
    def __init__(self, id, sum_edges, paths=[]):
        self.id = id
        self.sum_edges = sum_edges
        self.paths = paths

    def __eq__(self, other):
        if isinstance(other, Node):
            return self.id == other.id
        return False

    def __hash__(self):
        return self.id

    def __repr__(self):
        return f"Node(id={self.id},sum_edges={self.sum_edges})"


class Graph:
    def __init__(self, nodes):
        self.g = {}
        self.nodes = nodes
        self.edges = {}
        # Available weights
        self.aw = {}
        # Number of edges
        self.E = 0
        self.candidates = {}

    def add_edge(self, s_id, t_id, w=None):
        """
        Adds an edge to the graph with an optional weight
        """
        self.edges[(s_id, t_id)] = w
        self.edges[(t_id, s_id)] = w
        if s_id in self.g:
            self.g[s_id].add(t_id)
        else:
            self.g[s_id] = {t_id}

        if t_id in self.g:
            self.g[t_id].add(s_id)
        else:
            self.g[t_id] = {s_id}

        self.E = len(self.edges) // 2
        self.update_aw()

    def update_aw(self):
        """
        Updates available weights (aw). Available weights are weights 
        not assigned to any edge. 
        """
        self.aw = {i + 1 for i in range(self.E)}
        weights = {w for w in self.edges.values() if w}
        self.aw = self.aw.difference(weights)

    def update_candidates(self):
        """
        Updates candidate weights for each edge. Candidate weights are available weights 
        that can be assigned to an edge according to the state of the graph.  
        """
        self.candidates = {}
        for edge, w in self.edges.items():
            if not w:
                sid, tid = edge
                ub = self.upper_bound(sid, tid)
                candidates = [w for w in self.aw if w <= ub]
                self.candidates[(sid, tid)] = candidates

    def set_w(self, sid, tid, w):
        """
        Set weight w to the edge identified by source node id (sid) and 
        target node id (tid). Then update available weights and candidates.
        """
        self.edges[(sid, tid)] = w
        self.edges[(tid, sid)] = w
        self.update_aw()
        self.update_candidates()

    def unset_w(self, sid, tid):
        """
        Unset weight w of the edge identified by source id (sid) and target id (tid).
        Then update available weights and candidates.
        """
        self.edges[(sid, tid)] = None
        self.edges[(tid, sid)] = None
        self.update_aw()
        self.update_candidates()

    def upper_bound(self, s_id, t_id):
        """
        Determines the upper bound weight for the given edge according to the state of the graph.
        """
        s = self.nodes[s_id]
        t = self.nodes[t_id]

        def upper_bound(s, t):
            if not s.sum_edges:
                return self.E
            tot = 0
            aw = self.aw.copy()
            for neighbor_id in self.g[s.id]:
                if neighbor_id != t.id:
                    if self.edges[(neighbor_id, s.id)]:
                        tot += self.edges[(neighbor_id, s.id)]
                    else:
                        tot += min(aw)
                        aw.remove(min(aw))
            return min(self.E, s.sum_edges - tot)

        return min(upper_bound(s, t), upper_bound(t, s))

    def print_edges(self):
        seen = set()
        res = {}
        for edge, weight in self.edges.items():
            if edge in seen:
                continue
            a, b = edge
            seen.add((a, b))
            seen.add((b, a))
            res[edge] = weight
        print(res)

    def validate(self):
        """
        Validates the state of the graph:
        - The sum of all edges directly connected to a node
        - The paths (see function validate_paths)
        """
        for node in self.nodes:
            if node.sum_edges:
                tot = 0
                # if all direct edges set then has to equal to sum_edges
                if all(
                    self.edges[(node.id, neighbor_id)]
                    for neighbor_id in self.g[node.id]
                ):
                    if (
                        sum(
                            self.edges[(node.id, neighbor_id)]
                            for neighbor_id in self.g[node.id]
                        )
                        != node.sum_edges
                    ):
                        return False
                else:
                    for neighbor_id in self.g[node.id]:
                        if self.edges[(node.id, neighbor_id)]:
                            tot += self.edges[(node.id, neighbor_id)]
                    if tot > node.sum_edges:
                        return False
        if not self.validate_paths():
            return False
        return True

    def validate_paths(self):
        for node in self.nodes:
            if node.paths:
                for N in node.paths:
                    if not self.validate_path(node, N):
                        return False
        return True

    def validate_path(self, root, N):
        """
        Validates requirement:
        - There exists a non-self-intersecting path starting from this node where N is the sum of the weights of the edges on that path
        """
        seen = set()
        q = deque([(root.id, N)])
        while q:
            node_id, limit = q.popleft()
            seen.add(node_id)
            if limit == 0:
                return True
            if limit < 0:
                continue
            for neighbor_id in self.g[node_id]:
                if neighbor_id not in seen:
                    w = self.edges[(node_id, neighbor_id)]
                    if not w:
                        return True
                    q.append((neighbor_id, limit - w))
        return False

    def shortest_path(self, sid, tid):
        """
        Finds the shortest path between the given nodes
        """
        G = nx.Graph()
        G.add_nodes_from([node.id for node in self.nodes])
        for edge, w in self.edges.items():
            aid, bid = edge
            G.add_edge(aid, bid, weight=w)
        return nx.shortest_path(G, source=sid, target=tid, weight="weight")

    def decode_path(self, p):
        """
        Converts a path to the secret message
        """
        res_w = [self.edges[(p[i - 1], p[i])] for i in range(1, len(p))]
        alp = [0] + list(string.ascii_uppercase)
        message = [alp[w] for w in res_w]
        return "".join(message)

    def solve(self):
        """
        Solves the graph by finding the configuration of weights that satisfies the requirements
        """
        self.update_candidates()
        progress = len(self.edges) // 2

        def solve(edges):
            nonlocal progress
            if not edges:
                return True
            sid, tid = next(iter(edges))
            remaining_edges = {
                key: value
                for key, value in edges.items()
                if key != (sid, tid) and key != (tid, sid)
            }
            if len(remaining_edges) // 2 < progress:
                progress = len(remaining_edges) // 2
                print(f"Remaining edges to solve: {progress}...")
            # if the edge already has a weigth assigned, skip to next
            if edges[(sid, tid)]:
                return solve(remaining_edges)
            # Try every candidates for the given edge if there are any
            if self.candidates[(sid, tid)]:
                for w_candidate in self.candidates[(sid, tid)]:
                    self.set_w(sid, tid, w_candidate)
                    if self.validate() and solve(remaining_edges):
                        return True
                    # unset failed candidate
                    self.unset_w(sid, tid)
            return False
        return solve(self.edges)


def main():
    nodes = [
        Node(0, 17),
        Node(1, 3),
        Node(2, None, [19, 23]),
        Node(3, None),
        Node(4, None, [31]),
        Node(5, 54),
        Node(6, None, [6, 9, 16]),
        Node(7, 49),
        Node(8, None, [8]),
        Node(9, 60),
        Node(10, 79),
        Node(11, None),
        Node(12, 29),
        Node(13, 75),
        Node(14, None),
        Node(15, 25),
        Node(16, None),
        Node(17, 39),
    ]
    g = Graph(nodes)
    g.add_edge(0, 1)
    g.add_edge(0, 2)
    g.add_edge(1, 3)
    g.add_edge(2, 3, 12)
    g.add_edge(2, 5)
    g.add_edge(3, 7)
    g.add_edge(4, 5)
    g.add_edge(5, 9)
    g.add_edge(9, 7)
    g.add_edge(7, 8)
    g.add_edge(6, 9)
    g.add_edge(5, 10)
    g.add_edge(9, 10, 24)
    g.add_edge(9, 13)
    g.add_edge(7, 13, 20)
    g.add_edge(10, 11)
    g.add_edge(10, 12)
    g.add_edge(10, 17, 7)
    g.add_edge(12, 17)
    g.add_edge(12, 15)
    g.add_edge(13, 14)
    g.add_edge(13, 15)
    g.add_edge(15, 16)
    g.add_edge(16, 17)
    
    print("Total number of edges: ", g.E)

    start_time = time.time()
    g.solve()
    end_time = time.time()

    running_time = end_time - start_time
    print("Running time:", running_time, "seconds")
    p = g.shortest_path(3, 16)
    secret_message = g.decode_path(p)
    # Uncomment to see the solution
    #print(f"The secret message is: {secret_message}")


if __name__ == "__main__":
    main()
