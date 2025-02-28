import ast
from graphviz import Digraph

class GraphElements:
    def __init__(self, node_id, vertex_description):
        self.node_id = node_id
        self.vertex_description = vertex_description
        self.edges = []

class TestPathFinder:
    def __init__(self):
        self.vertices = {}
        self.start_vertex = None

    def add_vertex(self, vertex_id, vertex_description):
        if isinstance(vertex_id, int):
            if vertex_id not in self.vertices:
                self.vertices[vertex_id] = GraphElements(vertex_id, vertex_description)
            return self.vertices[vertex_id]
    def add_edge_between(self, from_id, to_id):
        if from_id in self.vertices and to_id in self.vertices:
            self.vertices[from_id].edges.append(to_id)

    def depth_first_traversal(self, start_id, path=None, visited_nodes=None):
        if path is None:
            path = []
        if visited_nodes is None:
            visited_nodes = set()

        if start_id in visited_nodes:  # Detect cycle and exit
            return

        visited_nodes.add(start_id)
        path.append(start_id)
        node = self.vertices[start_id]

        if not node.edges:  # Leaf node
            yield path[:]
        for edge in node.edges:
            yield from self.depth_first_traversal(edge, path, visited_nodes)

        path.pop()
        visited_nodes.remove(start_id)  # Backtrack

    def generate_control_flow_graph(self, tree):
        vertex_counter = [0]

        def next_vertex_id():
            vertex_counter[0] += 1
            return vertex_counter[0]

        def visit_node(node, parent_id=None):
            if isinstance(node, (ast.FunctionDef, ast.For, ast.While, ast.If, ast.Expr)):
                vertex_id = next_vertex_id()
                vertex_description = ""

                if isinstance(node, ast.FunctionDef):
                    vertex_description = f"Function: {node.name}"
                elif isinstance(node, ast.For):
                    target = ast.unparse(node.target).strip()
                    iter_ = ast.unparse(node.iter).strip()
                    vertex_description = f"For loop: for {target} in {iter_}"
                elif isinstance(node, ast.While):
                    condition = ast.unparse(node.test).strip()
                    vertex_description = f"While condition: {condition}"
                elif isinstance(node, ast.If):
                    condition = ast.unparse(node.test).strip()
                    vertex_description = f"If condition: {condition}"
                elif isinstance(node, ast.Expr) and isinstance(node.value, ast.Call):
                    vertex_description = f"Print: {ast.unparse(node.value).strip()}"

                self.add_vertex(vertex_id, vertex_description)
                if parent_id is not None:
                    self.add_edge_between(parent_id, vertex_id)

                parent_id = vertex_id

            for child in ast.iter_child_nodes(node):
                visit_node(child, parent_id)

            if isinstance(node, ast.For):
                loop_exit_id = next_vertex_id()
                self.add_vertex(loop_exit_id, "End of for loop")
                self.add_edge_between(parent_id, loop_exit_id)

            if isinstance(node, ast.While):
                loop_exit_id = next_vertex_id()
                self.add_vertex(loop_exit_id, "End of while loop")
                self.add_edge_between(parent_id, loop_exit_id)

        visit_node(tree)
        self.start_vertex = 1  # Assume the first vertex is the start

    def get_test_paths(self):
        paths = list(self.depth_first_traversal(self.start_vertex))
        return paths

    def calculate_test_path_complexity(self, path):
        path_complexity = 0
        for vertex_id in path:
            vertex_description = self.vertices[vertex_id].vertex_description
            if 'If condition' in vertex_description or 'For loop' in vertex_description or 'While condition' in vertex_description:
                path_complexity += 1
        return path_complexity

    def find_highest_complexity_path(self, execution_paths):
        max_complexity = -1
        highest_complexity_path = None

        for path in execution_paths:
            path_complexity = self.calculate_test_path_complexity(path)

            if path_complexity > max_complexity:
                max_complexity = path_complexity
                highest_complexity_path = path

        return highest_complexity_path, max_complexity

class CyclomaticComplexityCalculator(ast.NodeVisitor):
    def __init__(self,source_code):
        self.source_code=source_code
        self.decision_points = 0
        self.stack = []  # Stack to track nested constructs
        self.memo = {}   # Memoization cache for AST subtrees

    def visit(self, node):
        # Check if this node has already been processed (Memoization)
        node_id = id(node)
        if node_id in self.memo:
            self.decision_points += self.memo[node_id]
            return

        # Process the node and cache its results
        before = self.decision_points
        super().visit(node)
        self.memo[node_id] = self.decision_points - before

    def visit_If(self, node):
        """Count `if` and `elif`."""
        self.decision_points += 1
        self.stack.append('if')  # Track 'if' in the stack
        self.generic_visit(node)
        self.stack.pop()

    def visit_For(self, node):
        """Count `for` loops."""
        self.decision_points += 1
        self.stack.append('for')  # Track 'for' in the stack
        self.generic_visit(node)
        self.stack.pop()

    def visit_While(self, node):
        """Count `while` loops."""
        self.decision_points += 1
        self.stack.append('while')  # Track 'while' in the stack
        self.generic_visit(node)
        self.stack.pop()

    def visit_Try(self, node):
        """Count `try` blocks and their `except` handlers."""
        self.decision_points += 1
        self.stack.append('try')  # Track 'try' in the stack
        for handler in node.handlers:
            self.decision_points += 1  # Each `except` is a decision po
        self.generic_visit(node)
        self.stack.pop()

    def visit_With(self, node):
        """Count `with` statements."""
        self.decision_points += 1
        self.stack.append('with')  # Track 'with' in the stack
        self.generic_visit(node)
        self.stack.pop()

    def visit_FunctionDef(self, node):
        """Handle functions as separate scopes."""
        self.stack.append('function')  # Track 'function' in the stack
        self.generic_visit(node)
        self.stack.pop()
    
    def calculate_cyclomatic_complexity(self):
        """Calculate the Cyclomatic Complexity."""
        
        # Parse the code into an AST
        tree = ast.parse(self.source_code)
        self.visit(tree)
        return self.decision_points + 1
        
class VisualControlFlowGraph(ast.NodeVisitor):
    def __init__(self):
        self.mynodes = []  # List of nodes
        self.myedges = []  # List of edges as (from_node, to_node)
        self.current_node = "Start"  # Starting node
        self.node_counter = 1  # Unique identifier for each node
        self.loop_stack = []  # To track if we are inside a loop
        self.break_nodes = []  # To track break locations outside of loops
        self.continue_nodes = []  # To track continue locations
        self.expr_node = []
        self.last_stmt_node=[]
    
    def analyze(self, tree):
      """Analyze a parsed AST tree."""
      self.visit(tree)
      return self.mynodes, self.myedges

    def add_node(self, label):
        """Add a node and update current node."""
        node_id = f"Node{self.node_counter}"
        self.mynodes.append((node_id, label))
        self.node_counter += 1
        return node_id

    def add_edge(self, from_node, to_node):
        """Add an edge between two nodes only if it doesn't already exist."""
        if (from_node, to_node) not in self.myedges:
            self.myedges.append((from_node, to_node))

    def add_back_edge(self, last_stmt_node, target_node):
        """Handles the back edge from a block to the loop or function."""
        if last_stmt_node:
            self.add_edge(last_stmt_node, target_node)

    def visit_FunctionDef(self, node):
        """Handle function definitions."""
        entry_node = self.add_node(f"Function: {node.name}")
        self.add_edge(self.current_node, entry_node)
        self.current_node = entry_node

        for stmt in node.body:
            self.visit(stmt)

        exit_node = self.add_node("End Function")
        self.add_edge(self.current_node, exit_node)
        self.current_node = exit_node

    def visit_If(self, node):
        """Handle if-elif-else structures without redundancy."""
        # Handle the main 'if' condition
        condition_node = self.add_node(f"If: {ast.unparse(node.test)}")
        self.add_edge(self.current_node, condition_node)
        # True branch of the 'if'
        self.current_node = condition_node
        # Process all statements in the 'if' body
        last_true_if_stmt=None
        for stmt in node.body:
            self.visit(stmt)
            if self.current_node == self.expr_node :
               last_true_if_stmt = self.expr_node  # Track the last statement in the 'if'
            elif self.current_node == self.continue_nodes :
                last_true_if_stmt = self.continue_nodes  # Track the last statement in the 'if'
            elif self.current_node == self.break_nodes :
                last_true_if_stmt = self.break_nodes # Track the last statement in the 'if'
            if self.loop_stack:
               self.loop_condition = self.loop_stack[-1]
               self.add_back_edge(last_true_if_stmt, self.loop_condition)

        # Handle the 'orelse' branch
        self.current_node = condition_node  # Reset to the condition node for branching
        orelse_node = node  # Start with the current If node
        while orelse_node.orelse:
            # Check if the next 'orelse' is an if (elif case)
            next_node = orelse_node.orelse[0]
            if isinstance(next_node, ast.If):
                elif_condition_node = self.add_node(f"Elif: {ast.unparse(next_node.test)}")
                self.add_edge(self.current_node, elif_condition_node)
                # True branch for the 'elif'
                self.current_node = elif_condition_node
                # Process all statements in the body of this 'elif'
                last_elif_true_stmt=None
                for stmt in next_node.body:
                    self.visit(stmt)
                    if self.current_node == self.expr_node :
                        last_elif_true_stmt = self.expr_node  # Track the last statement in the 'if'
                    elif self.current_node == self.continue_nodes :
                        last_elif_true_stmt = self.continue_nodes  # Track the last statement in the 'if'
                    elif self.current_node == self.break_nodes :
                        last_elif_true_stmt = self.break_nodes # Track the last statement in the 'if'
                    if self.loop_stack:
                        self.loop_condition = self.loop_stack[-1]
                        self.add_back_edge(last_elif_true_stmt, self.loop_condition)
                
                # Move to the next 'orelse'
                self.current_node = elif_condition_node
                orelse_node = next_node
            else:
                # Process all statements in the 'else' block
                for stmt in orelse_node.orelse:
                    self.visit(stmt)
                break  # Exit after handling the else block


    def visit_Expr(self, node):
        """Handle expressions (e.g., print)."""
        self.expr_node = self.add_node(f"Expr: {ast.unparse(node.value)}")
        self.add_edge(self.current_node,self.expr_node)
        self.current_node = self.expr_node
        self.last_stmt_node=self.expr_node

    def visit_While(self, node):
        """Handle while loops."""
        condition_node = self.add_node(f"While: {ast.unparse(node.test)}")
        self.add_edge(self.current_node, condition_node)
        self.current_node = condition_node

        self.loop_stack.append(condition_node)  # Mark that we are in a loop

        last_statement_node = None
        for stmt in node.body:
            self.visit(stmt)
            last_statement_node = self.current_node

        # Add back edge from the last statement in the loop to the loop condition
        self.add_back_edge(last_statement_node, condition_node)

        self.loop_stack.pop()  # Exit the loop

        self.after_loop = self.add_node("After Loop")
        self.add_edge(condition_node, self.after_loop)
        self.current_node = self.after_loop

    def visit_For(self, node):
        """Handle for loops."""
        iter_node = self.add_node(f"For: {ast.unparse(node.target)} in {ast.unparse(node.iter)}")
        self.add_edge(self.current_node, iter_node)
        self.current_node = iter_node

        self.loop_stack.append(iter_node)  # Mark that we are in a loop

        last_statement_node = None
        for stmt in node.body:
            self.visit(stmt)
            last_statement_node = self.current_node

        # Add back edge from the last statement in the loop to the loop condition
        self.add_back_edge(last_statement_node, iter_node)

        self.loop_stack.pop()  # Exit the loop
        after_loop = self.add_node("After Loop")
        self.add_edge(iter_node, after_loop)
        self.current_node = after_loop

    def visit_Break(self, node):
        """Handle break statements."""
        # Track break statements, need to connect break to the exit of the loop
        if self.loop_stack:
            loop_condition = self.loop_stack[-1]  # The current loop condition
            self.break_nodes = self.add_node("Break")
            self.add_edge(self.current_node, self.break_nodes)
            self.add_edge(self.break_nodes, loop_condition)  # Break to loop exit or next logic

    def visit_Continue(self, node):
        """Handle continue statements."""
        # Track continue statements, which skip to the next iteration
        if self.loop_stack:
            loop_condition = self.loop_stack[-1]  # The current loop condition
            self.continue_nodes = self.add_node("Continue")
            self.add_edge(self.current_node, self.continue_nodes)
            self.add_edge(self.continue_nodes, loop_condition)  # Continue to the next iteratio
    def visualize_cfg(self):
     # Create a directed graph
     dot = Digraph()
     # Add nodes
     for node_id, label in self.mynodes:
        dot.node(
            node_id,
            label=label,
            nodesep='1.0',
            ranksep='1.2',
            rankdir='TB',
            shape="ellipse",
            length='2.5',
            width='2.8',  # Adjusted size for better visualization
            fixedsize="true",
            style="filled",
            fillcolor="lightblue",
            fontsize="12",
            fontcolor="black",
            color="black"
        )

     # Add edges
     for from_node, to_node in self.myedges:
        dot.edge(
            from_node,
            to_node,
            color="black",
            style="solid",
            penwidth="1.5",
            arrowhead="normal"
        )

     # Render and view the graph
     dot.render("cfg", format="svg", cleanup=True)  # Generates a PNG file
     dot.view("cfg")  # Opens the generated graph

def main():
    file_path = r"C:\Users\LENOVO\Desktop\BSCS\codes\python\python project\code sample.py"
    with open(file_path, "r") as f:
        source_code = f.read()
    tree = ast.parse(source_code)
    analyzer = VisualControlFlowGraph()
    gnodes, gedges = analyzer.analyze(tree)
    
    # Output results
    print("Nodes:")
    for node_id, label in gnodes:
        print(f"{node_id}: {label}")

    print("\nEdges:")
    for from_node, to_node in gedges:
        print(f"{from_node} -> {to_node}")
    
    # Visualize the CFG
    analyzer.visualize_cfg()
    cfg = TestPathFinder()
    cfg.generate_control_flow_graph(tree)
    test_paths = cfg.get_test_paths()

    # First task: Generate CFG and get execution paths
    print("\nReadable Execution Paths:")
    for i, path in enumerate(test_paths, 1):
        print(f"Path {i}: {' -> '.join(cfg.vertices[vertex].vertex_description for vertex in path)}")
    
    # Second task: Calculate Cyclomatic Complexity
    try:
        complexity = CyclomaticComplexityCalculator(source_code)
        print(f"\nCyclomatic Complexity: {complexity.calculate_cyclomatic_complexity()}")
    except Exception as e:
        print(f"Error analyzing the file: {e}")

    # Third task: Find Most Complex Path
    highest_complexity_path, max_complexity = cfg.find_highest_complexity_path(test_paths)
    if highest_complexity_path:
        print(f"\nMost Complex Path :")
        path_description = ' -> '.join(cfg.vertices[vertex_id].vertex_description for vertex_id in highest_complexity_path)
        print(path_description )
        print("\n")

    else:
        print("No valid path found.")

if __name__ == "__main__":
    main()