
import pygraphviz as pgv
import matplotlib.pyplot as plt
import matplotlib.image as mpimg
import copy

# The implementation is stored in a subcombinator class

# # nodes are defined as a triple of unique node identifier, term, number of incoming edges

# # Terms are defined as an array of subterms that are either a string or an array.
# # This mimics the behaviour of variables and brackets and allows to easily identify what is being
# # referenced by the lambda abstractions

# # Incoming port edges are stored here as well as it makes checking for the one incoming port edge
# # condition of rule 1 much easier, this isn't required for the tree implementation but is left in for portability to graph reduction.
      
# nodes = [
    
# ( 1, [ "y" , [ "λf" , "λx" , "f" ,  [ "f", "x" ] ] , "s" , "z" ], 1 ) ,
# ( 2, [ "λf" , "λx" , "f", [ "f", "x" ] ] , 1 ) ,
# ( 3, ["s"], 1) ,
# ( 4, ["0"], 1)
# ]

# # edges

# # edges are stored as an array of arrays with the first entry the node identifier of the base term
# # of that edge. This allows for more efficient copying of all edges that lead off from a certain node

# node_edges = [
        
#         [ 1 , ("y", 2) , ("s", 3), ("z", 4 ) ]
#   ]

class subcombinator:
    
    def __init__ (self, lambda_term_string):
        
        self.lambda_term_string = lambda_term_string
        
        self.variable_list = ['a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm', 'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v', 'x', 'y', 'z']
        
        self.nodes = []
        
        self.node_edges = []
        
        self.constants = ['S', '0']
        
        # A running count of the number of nodes is required to keep defining a unique node identifier
        self.term_count = 0
        
        self.normal_form_subcombinator(lambda_term_string)
        
        self.potential_reductions = []
        
        self.print_graph(0)
    
    # Applies steps until no further are possible and prints information and the pygraphviz image
    
    def add_potential_reduction(self, reduction):
        
        self.potential_reductions.append(reduction)
    
    
    def reset_potential_reductions(self):
        
        self.potential_reductions = []
    
    
    def run_steps ( self, pygraphviz_graph_boolean ):
    
        step = 0
        
        reduction_occured = True
        
        while reduction_occured == True:
            
            step = step + 1
            reduction_occured = self.reduce_one_step( )
            nodes_to_print = copy.deepcopy(self.nodes)
            node_edges_to_print = copy.deepcopy(self.node_edges)
            
            subcombinator_to_print = equivalent_lambda_term_subcombinator ( nodes_to_print, node_edges_to_print)
            output_lambda_string = subcombinator_to_print.subcombinator_to_lambda_string()
            
            print()
            
            print("Step: "+str(step))    
            
            print("Step output is: "+output_lambda_string)
            
            if pygraphviz_graph_boolean == False:
            
                self.print_subcombinator_node_and_edge_arrays
        
            if pygraphviz_graph_boolean == True:
            
                self.print_graph(step)

        return
    
    
    def reduce_one_step (self):
    
    # Check all edges by iterating first through each base. Check for rules 1 and 2 first so that 
    # all posible work is carried out before duplication, to save repeat steps.
    
        reduced_boolean = False
    
        self.reset_potential_reductions()
    
        for node_edge in self.node_edges:
            
            base_identifier = node_edge[0]
            base_term = self.get_term(base_identifier)
            free_variables_base_term = self.get_free_variables(base_term)
            
            # Check the actual edges leading off from this base
            
            for edge in node_edge[1:]:
            
                port_label, top_identifier = edge
                top_term = self.get_term(top_identifier)
                
                #Check for delete rule
                
                if port_label not in free_variables_base_term:
                    
                    self.add_potential_reduction( ("Delete", (base_identifier, top_identifier, port_label) ) )
                
                # Check for axiom rule
                
                if len(base_term) == 1:
                    
                    if base_term[0] == port_label:
                        
                        self.add_potential_reduction( ( "Axiom", (base_identifier, top_identifier) ) )
                
                # Check for beta reductionn
                
                if len(top_term[0]) >=2:
                
                    if top_term[0][0] == 'λ':
                        
                        if self.get_incoming_edge_count( top_identifier ) == 1:
                            
                                self.check_beta_reduction_rule(base_identifier, base_term, base_term, top_identifier, top_term, port_label)  
        
                # Check for duplication rule               
                        
                port_label_occurrence = self.get_variable_count(base_term, port_label)
                
                if port_label_occurrence >= 2:
                    
                    self.add_potential_reduction( ("Duplication", (base_identifier, base_term, port_label, top_identifier) ) )
        
        
        if self.potential_reductions != []:
        
        #********* UNCOMMENT CHOOSE_REDUCTION AND COMMENT OUT APPLY_REDUCTION TO TOGGLE BETWEEN TWO RUN OPTIONS*******
        
            # self.choose_reduction( self.potential_reductions )    
        
            self.apply_reduction( self.potential_reductions )
        
            return True
        
        else:
            
            print("No further reductions possible")
            print()
            final_string = self.subcombinator_to_lambda_string()
            print()
            
            return False
        
        
        

    def apply_reduction(self, potential_reductions ):
        
        self.print_potential_reductions()
        
        # print()
        
        for reduction in potential_reductions:
            
            reduction_name, reduction_information = reduction
            
            if reduction_name == "Delete":
                
                base_identifier, top_identifier, port_label = reduction_information
                print("Delete rule activated between "+str(base_identifier)+" and "+str(top_identifier))
                self.apply_delete_rule(base_identifier, top_identifier, port_label)
                
                return
        
        for reduction in potential_reductions:
            
            reduction_name, reduction_information = reduction
            
            if reduction_name == "Axiom":
                
                base_identifier, top_identifier = reduction_information
                print("Axiom rule activated between "+str(base_identifier)+" and "+str(top_identifier))
                self.apply_axiom_rule(base_identifier, top_identifier)
                
                return
                
                
        for reduction in potential_reductions:
            
            reduction_name, reduction_information = reduction
            
            if reduction_name == "β reduction":
                
                base, base_term, top, top_term, variable = reduction_information
                print("β reduction activated between "+str(base)+" and "+str(top))
                self.apply_beta_reduction_rule(base, base_term, top, top_term, variable)
                
                return
         
                
        for reduction in potential_reductions:
            
            reduction_name, reduction_information = reduction
            
            if reduction_name == "Duplication":
                
                base_identifier, base_term, port_label, top_identifier = reduction_information
                print("Duplication rule activated at "+str(base_identifier) )
                self.apply_duplication_rule(base_identifier, base_term, port_label, top_identifier)
                
                return
 
    
    def print_subcombinator_node_and_edge_arrays( self ):

        print("Nodes: ")        
        for node in self.nodes:
            print(node)
            
        print()
          
        print("Edges: ")
        for edge in self.node_edges:
            print(edge)
            
        return
    
    
    def print_potential_reductions(self):
        
        reduction_number = 1
        
        print("Potential reductions are:")
        
        for reduction in self.potential_reductions:
            
            reduction_name, reduction_information = reduction
            
            if reduction_name == "Delete":
                
                base_identifier, top_identifier, port_label = reduction_information
                print( str(reduction_number)+": Delete between "+str(base_identifier)+" and "+str(top_identifier) )
                reduction_number = reduction_number + 1
            
            if reduction_name == "Axiom":
                
                base_identifier, top_identifier = reduction_information
                print( str(reduction_number)+": Axiom between "+str(base_identifier)+" and "+str(top_identifier) )
                reduction_number = reduction_number + 1        
    
            if reduction_name == "β reduction":
                
                base_identifier, base_term, top_identifier, top_term, variable = reduction_information
                print( str(reduction_number)+": β reduction between "+str(base_identifier)+" and "+str(top_identifier)+" along "+variable )
                reduction_number = reduction_number + 1
                   
            if reduction_name == "Duplication":
                
                base_identifier, base_term, port_label, top_identifier = reduction_information
                print( str(reduction_number)+": Duplication at "+str(base_identifier)+" with "+str(port_label)+" and "+str(top_identifier) )
                reduction_number = reduction_number + 1
                
        print()
        return
            

    def choose_reduction(self, potential_reductions ):
        
        reduction_number = 1
        
        for reduction in potential_reductions:
            
            reduction_name, reduction_information = reduction
            
            if reduction_name == "Delete":
                
                base_identifier, top_identifier, port_label = reduction_information
                print( "Press "+str(reduction_number)+" for Delete between "+str(base_identifier)+" and "+str(top_identifier) )
                reduction_number = reduction_number + 1
            
            if reduction_name == "Axiom":
                
                base_identifier, top_identifier = reduction_information
                print( "Press "+str(reduction_number)+" for Axiom between "+str(base_identifier)+" and "+str(top_identifier) )
                reduction_number = reduction_number + 1
            
            if reduction_name == "β reduction":
                
                base_identifier, base_term, top_identifier, top_term, variable = reduction_information
                print( "Press "+str(reduction_number)+" for β reduction between "+variable+" at "+str(base_identifier)+" and "+str(top_term)+" at "+str(top_identifier) )
                reduction_number = reduction_number + 1
  
            if reduction_name == "Duplication":
                
                base_identifier, base_term, port_label, top_identifier = reduction_information
                print( "Press "+str(reduction_number)+" for Duplication at "+str(base_identifier)+" with "+str(port_label)+" and "+str(top_identifier) )
                reduction_number = reduction_number + 1
                
        reduction_choice = input("Reduction choice: ")
        reduction_int = int(reduction_choice)
        reduction_int = reduction_int - 1
        reduction = potential_reductions[reduction_int]
        reduction_name, reduction_information = reduction
            
        if reduction_name == "Delete":
            
            base_identifier, top_identifier, port_label = reduction_information
            self.apply_delete_rule(base_identifier, top_identifier, port_label)
        
        if reduction_name == "Axiom":
            
            base_identifier, top_identifier = reduction_information
            self.apply_axiom_rule(base_identifier, top_identifier)
        
        if reduction_name == "β reduction":
            
            base, base_term, top, top_term, variable = reduction_information
            self.apply_beta_reduction_rule(base, base_term, top, top_term, variable)
            
        if reduction_name == "Duplication":
            
            base_identifier, base_term, port_label, top_identifier = reduction_information
            self.apply_duplication_rule(base_identifier, base_term, port_label, top_identifier)
            
        return
                
    
    
    def check_beta_reduction_rule(self, base, base_term, term_array, top, top_term, port_label):
        
        original_base_term = self.get_term( base )
        
        original_base_term_free_variables = self.get_free_variables(original_base_term)
        
        print("Original base term free variables are: "+str(original_base_term_free_variables))
        
        array_index = -1
        
        for subterm in term_array:
        
            array_index = array_index + 1    
        
            if isinstance( subterm, list):
                    
                    self.check_beta_reduction_rule( base, base_term, subterm, top, top_term, port_label)
        
                    continue
        
        
            if isinstance( subterm, str):
            
                if subterm[0] == 'λ':
                    
                    continue
        
                elif subterm == port_label:
                    
                    M_location = array_index + 1
                    
                    if len(term_array) > M_location:
                        
                        M = term_array[M_location]
                        
                        # print("M is: "+str( M ))
                        
                    else:
                        
                        M = []
                    
                    port_label_in_free_variables_yM = False
                    
                    free_variables_in_M = self.get_free_variables( M )

                    if port_label in free_variables_in_M:
                        
                        port_label_in_free_variables_yM = True
                        
                        return
                    
                    free_variables_yM = free_variables_in_M
                    # print("free variables in M are: "+str(free_variables_yM))
                    # print("y is: "+port_label)
                    free_variables_yM.append(port_label)
                    # print("free variables in yM are: "+str(free_variables_yM))
                    
                    if port_label_in_free_variables_yM == False:
                    
                        all_free_variables_in_yM_free_in_base_term = True
                        
                        if free_variables_yM != []:
                        
                            for free_variable in free_variables_yM:
                                
                                if free_variable not in original_base_term_free_variables:
                                    
                                    all_free_variables_in_yM_free_in_base_term = False
                                    
                                    return
                        
                            if all_free_variables_in_yM_free_in_base_term == True:
                            
                                P_without_yM = copy.deepcopy(base_term)
                                removed_boolean, M = self.remove_M(P_without_yM, port_label)
                                variable_deleted = self.delete_y(P_without_yM, port_label)
                                free_variables_in_P_without_yM = self.get_free_variables(P_without_yM)
                                intersection_fv_P_and_fc_yM = False
                            
                                if free_variables_yM != []:
                            
                                    for free_variable_yM in free_variables_yM:
                                        
                                         if free_variable_yM in free_variables_in_P_without_yM:
                                            
                                             intersection_fv_P_and_fc_yM = True
                                             
                                             return
                            
                                if intersection_fv_P_and_fc_yM == False:
                            
                                    self.add_potential_reduction( ( "β reduction", (base, base_term, top, top_term, subterm ) ) )
            
            return
            
        return                 


    def apply_beta_reduction_rule(self, base, base_term, top, top_term, abstracted_variable):

        base_term_string = self.lambda_array_to_string( base_term )     
        print("P{yM} is: "+base_term_string+" at "+str(base))
        print("y is: "+abstracted_variable )
        
        top_term_string = self.lambda_array_to_string( top_term )
        
        print("λx.N is: "+top_term_string + " at "+str(top) )
        print("x is: "+str ( top_term[0][1] ) )
        
        new_port_label = top_term[0][1:]
        
        # Deep copy is required to have a new memory pointer for the term array and also any subterms that are arrays
        # This can be a computationally slow process, as it allows for deep copying of many different objects, so a self defined
        # function specifically for arrays could be more efficient
        
        new_top_term = copy.deepcopy(top_term)
        
        new_top_term = new_top_term[1:]
        
        if len(new_top_term) == 1:
            
            if isinstance( new_top_term[0], list):
            
                new_top_term_without_uneeded_brackets = []
                
                for subterm in new_top_term[0]:
                    
                    new_top_term_without_uneeded_brackets.append(subterm)
                    
                new_top_term = new_top_term_without_uneeded_brackets
        
        new_top_term_string = self.lambda_array_to_string( new_top_term )
        
        print("N is: "+new_top_term_string)
        
        self.edit_node( top, new_top_term)
        
        M_Found_Boolean, M = self.remove_M(base_term, abstracted_variable)
        
        if M != []:
        
            new_node_identifier = self.new_node( M )
            M_string = self.lambda_array_to_string( M )
            print("M is: "+M_string+" at: "+str(new_node_identifier) )
            self.new_edge ( top, (new_port_label, new_node_identifier ) )
            
            #reassign free variables
            
            free_variables = self.get_free_variables ( M )
            print("Free variables of M are: "+str( free_variables ) )
            node_edge_index = -1
            
            for node_edge in self.node_edges: 
                
                node_edge_index = node_edge_index + 1
                
                if node_edge[0] == base:
                    
                    edge_index = 0
                    
                    for edge in node_edge[1:]:
                        
                        edge_index = edge_index + 1
                        port_label, top_node = edge
                        
                        if port_label in free_variables:
                            
                            moved_edge = self.node_edges[node_edge_index].pop(edge_index)
                            edge_index = edge_index - 1
                            self.reduce_incoming_edge_count(top_node)
                            self.new_edge( new_node_identifier, moved_edge)
                            
                            if len(self.node_edges[node_edge_index]) == 1:
                                
                                del self.node_edges[node_edge_index]
        return



    def remove_M(self, base_term, variable):
        
        M = []
        array_index = 0
        M_location = -1
        M_found = False
        
        for subterm in base_term:
        
            if isinstance(subterm, str):
        
                if array_index == M_location:
                        
                        M = base_term.pop(array_index)
                        M_found = True
                        
                        return M_found, M
                        
                elif subterm == variable:
                        
                    M_location = array_index + 1
                    array_index = array_index + 1
                    
                else:
                    
                    array_index = array_index + 1
                    
                
            if isinstance(subterm, list):
                
                if array_index == M_location:
                
                        M = base_term.pop(array_index)
                        M_found = True
                        
                        return M_found, M
                
                else:
                    
                    array_index = array_index + 1
                    M_found, M = self.remove_M(subterm, variable)
                    
                    if M_found == True:
                        
                        return M_found, M
                    
        return M_found, M
                    
    
    def delete_y(self, term, variable):

        variable_location = -1        
        variable_deleted = False

        for subterm in term:
            
            variable_location = variable_location + 1
            
            if isinstance(subterm, str):
                
                if subterm == variable:
                    
                    del term[variable_location]
                    
                    return variable_deleted
                
                else:
                    
                    continue
                
            else:
                
                variable_deleted = self.delete_y(subterm, variable)
                
                if variable_deleted == True:
                    
                    return term, variable_deleted
                
                else:
                    
                    continue
                
            print("Variable not found")

            return variable_deleted          
                    
    
    # Applies delete rule 

    def apply_delete_rule(self, staying_node, deleted_node, variable):
        
        #Delete the edge
        
        node_edge_index = -1
        
        for node_edge in self.node_edges:
            
            node_edge_index = node_edge_index + 1
            base_identifier = node_edge[0]
            
            if base_identifier == staying_node:
                
                connection_index = 0
                
                for connection in node_edge[1:]:
                    
                    connection_index = connection_index + 1
                    port_label, top_node = connection
                    
                    if port_label == variable:
                        
                        del self.node_edges[node_edge_index][connection_index]
                        
                        if len(self.node_edges[node_edge_index]) == 1:
                            
                            del self.node_edges[node_edge_index]
                
        self.delete_node_and_connections( deleted_node )
        
        return
        
    
    
    def delete_node_and_connections( self, deleted_node ):     
    
        node_index = -1               
        
        for node in self.nodes:
            
            node_index = node_index + 1
            node_identifier, node_term, incoming_edges = node
            
            if node_identifier == deleted_node:
                
                del self.nodes[node_index]
                
                node_edge_index = -1
                
                for node_edge in self.node_edges:
                    
                    base_identifier = node_edge[0]
                    
                    if base_identifier == deleted_node:
                        
                        for connection in node_edge[1:]:
                            
                            port_label, top_node = connection
                            self.delete_node_and_connections( top_node )
                            del self.node_edges[node_edge_index]
                            
        return
    
    
    
    def apply_axiom_rule(self, deleted_node, staying_node):
        
        self.delete_node( deleted_node )
        node_edge_index = -1
        
        for node_edge in self.node_edges:
            
            node_edge_index = node_edge_index + 1
            edge_index = 0
            
            for edge in node_edge[1:]:
                
                edge_index = edge_index + 1
                port_label, top = edge
                
                if top == deleted_node:
                    
                    self.node_edges[node_edge_index][edge_index] = (port_label, staying_node)
                    
        return
                        
                            
                
    # Rule 3, renaming of second occurrence of a variable and an addition of a edge for this variable
    # has been combined with rule 4, additional node for this new edge           
     
    def apply_duplication_rule( self, base, base_term, port_label, top_node):
        
        top_term = self.get_term(top_node)
        copied_top_term = copy.deepcopy(top_term)
        fresh_variable = self.get_unique_renaming(base_term, port_label)
        print("Original variable is: "+port_label)
        print("Fresh variable is: "+fresh_variable)

        variable_count, term, sub_term_index, new_variable = self.rename_second_occurrence( base_term, port_label, 0, fresh_variable)
        duplicated_node_identifier = self.new_node( copied_top_term )
        
        self.new_edge ( base, ( fresh_variable, duplicated_node_identifier ) )
        
        # This is a recurssive function to copy the full subtree
        self.copy_nodes_and_edges( top_node , duplicated_node_identifier)
        
        return
                    
                    
    def copy_nodes_and_edges( self, from_node_identifier, to_node_identifer ):
               
        for node_edge in self.node_edges:
            
            if node_edge[0] == from_node_identifier:
                
                for edge in node_edge[1:]:
                    
                    port_label, top_node_identifier = edge
                    top_node_term = self.get_term( top_node_identifier )
                    copied_top_node_term = copy.deepcopy(top_node_term)
                    copied_term_identifier = self.new_node(copied_top_node_term)
                    self.new_edge( to_node_identifer, ( port_label, copied_term_identifier) )
                    self.copy_nodes_and_edges( top_node_identifier, copied_term_identifier )
                    
        return

                    
    def rename_second_occurrence( self, term, variable, variable_count, new_variable):
        
        sub_term_index = -1
        
        for subterm in term:
            
            sub_term_index = sub_term_index + 1
            
            if isinstance(subterm, str):
            
                if subterm == variable:
                    
                    variable_count = variable_count + 1
    
                    if variable_count == 2:
                        
                        term[sub_term_index] = new_variable
                        
                        return variable_count, term, sub_term_index, new_variable
                        
            if isinstance(subterm, list):
                
                variable_count, subterm, subsub_term_index, new_variable = self.rename_second_occurrence( subterm, variable, variable_count, new_variable)
                
                return variable_count, term, sub_term_index, new_variable
            
        return


    def get_unique_renaming(self, term, variable):
        
        new_variable = variable+"*"
        
        unique_boolean = False
        
        while unique_boolean == False:
            
            unique_boolean = self.check_unique_variable(term, new_variable)
            
            if unique_boolean == False:
                
                new_variable = new_variable+"*"
                
        return new_variable
                    
                    
    def check_unique_variable(self, term, variable):
        
        unique_boolean = True
        
        for subterm in term:
                
            if isinstance(subterm, str):
                    
                if subterm == variable:
                        
                    unique_boolean = False
                    
                    return unique_boolean
                    
            if isinstance(subterm, list):
                    
                unique_boolean = self.check_unique_variable(subterm, variable)
                
                if unique_boolean == False:
                    
                    return unique_boolean
                
        return unique_boolean


    def print_graph(self, step):
        
        net_graph = pgv.AGraph( rankdir="BT")
        
        if len(self.node_edges) == 0:
            
            for node in self.nodes:
                
                node_identifier, node_term, number_incoming_edges = node
                net_graph.add_node( (node_identifier, node_term) )
        
        for node_edge in self.node_edges:
            
            lhs_identifier = node_edge[0]
              
            for edge in node_edge[1:]:
                
                port_label , rhs_identifier = edge
                lhs_term = self.get_term ( lhs_identifier )
                lhs_string = self.lambda_array_to_string(lhs_term)
                rhs_term = self.get_term ( rhs_identifier )
                rhs_string = self.lambda_array_to_string(rhs_term)
                net_graph.add_edge( ( lhs_identifier, lhs_string ) , (rhs_identifier, rhs_string) , label=port_label)


        # This defines the style of the graph
        net_graph.node_attr.update(fontname="Helvetica")
        net_graph.node_attr.update(fontsize = 14.0)
        net_graph.edge_attr.update(fontname="Helvetica Italic",fontcolor='red', fontsize=14.0)
        net_graph.layout(prog='dot')
        
        # This creates a new file with the image of the graph
        name = self.lambda_term_string+", step "+str(step)+".png"
        net_graph.draw(name)
            
        #This displays the image of the graph in the IDE
        img = mpimg.imread(name)
        plt.imshow(img)
        plt.axis('off')
        plt.show()
        
        return
            
     # Given a term, adds a unique node with that term. Allowances are made for the term being an array or string
     
    def new_node(self, term):
        
        if isinstance(term, list):   
        
            self.term_count = self.term_count + 1
            self.nodes.append( ( self.term_count, term, 0 ) )
        
            return self.term_count
        
        if isinstance(term, str):
        
            self.term_count = self.term_count + 1
            self.nodes.append( ( self.term_count, [term], 0 ) )
        
            return self.term_count
    
    
    # Deletes a node. Doesn't reduce node count as might then have overlapping names.
    
    def delete_node(self, identifier):
        
        node_index = -1
        
        for node in self.nodes:
            
            node_index = node_index + 1
            
            if node[0] == identifier:
                
                del self.nodes[node_index]
        
        node_edge_index = -1
        
        for node_edge in self.node_edges:
            
            node_edge_index = node_edge_index + 1
            
            if node_edge[0] == identifier:
                
                del self.node_edges[node_edge_index]
            
        return
            
    # Adds a new edge. Here base is a node identifier and edge is a tuple of port_label and top_node identifier
    # The function checks to see if an array of edges with that base already exists, and makes a new one if not
    # This function increases the incoming edge count of the top node.
    
    def new_edge(self, base, edge):
        
        port_label, top_node = edge
        self.increase_incoming_edge_count( top_node )
        node_edge_index = -1
        
        for node_edge in self.node_edges:
            
            node_edge_index = node_edge_index + 1
            
            if node_edge[0] == base:
                
                self.node_edges[node_edge_index].append(edge)
                
                return
            
        self.node_edges.append( [ base, edge ])
        
        return
    

    # Returns the number of incoming edges for a node identifer

    def get_incoming_edge_count(self, identifier):
        
        for node in self.nodes:
            
            this_identifier, term, incoming_edge_count = node
            
            if identifier == this_identifier:
                
                return incoming_edge_count
    
    # Increases incoming edge count
    
    def increase_incoming_edge_count(self, identifier):
        
        node_index = -1
        
        for node in self.nodes:
            
            node_index = node_index + 1
            this_identifier, term, incoming_edge_count = node
            
            if identifier == this_identifier:
                
                new_incoming_edge_count = incoming_edge_count + 1
                self.nodes[node_index] = (this_identifier, term, new_incoming_edge_count)
                
                return
                
    
    # Decreases incoming edge count            
    
    def reduce_incoming_edge_count(self, identifier):          
                
        node_index = -1
        
        for node in self.nodes:
            
            node_index = node_index + 1
            this_identifier, term, incoming_edge_count = node
            
            if identifier == this_identifier:
                
                new_incoming_edge_count = incoming_edge_count - 1
                self.nodes[node_index] = (this_identifier, term, new_incoming_edge_count)
                
                return
    
    
    # To edit a node
    
    def edit_node(self, identifier, new_term):
        
        node_index = -1
        
        for node in self.nodes:
            
            node_index = node_index + 1
            this_identifier, term, incoming_port_count = node
            
            if this_identifier == identifier:
                
                self.nodes[node_index] = (identifier, new_term, incoming_port_count)
                
                
    def get_free_variables (self, term):
        
        variables = []
        bound_variables = []
        array_index = 0
        
        if isinstance (term, str):
            
            if term[0] == 'λ':
                
                return []
            
            elif term in self.constants:
                
                return []
            
            else:
                
                return [term]
            
        if isinstance (term, list):
        
            for subterm in term:
                
                if isinstance(subterm, str):
                    
                    if subterm[0] == 'λ':
                        
                        bound_variables.append ( subterm[1] )
                        
                    elif subterm in self.constants:
                        
                        continue
                        
                    else:
                        
                        variables.append (subterm)
                
                if isinstance(subterm, list):
                
                    subterm_variables = self.get_free_variables( subterm )
                    variables = variables + subterm_variables
                
            
            bound_variable_set = set(bound_variables)
            free_variables = [ variable for variable in variables if variable not in bound_variable_set ]
            
            return free_variables
        
        
    def get_used_variables (self, term):
        
        used_variables = []
        array_index = 0
        
        if isinstance (term, str):
            
            if term[0] == 'λ':
                
                if term[1:] not in used_variables:
                
                    used_variables.append(term[1:])
            
            else:
                
                if term not in used_variables:
                
                    used_variables.append(term)
            
        if isinstance (term, list):
        
            for subterm in term:
                
                subterm_used_variables = self.get_used_variables(subterm)
                
                if subterm_used_variables != []:
                
                    for used_variable in subterm_used_variables:
                        
                        if used_variable not in used_variables:
                    
                            used_variables.append(used_variable)
            
        return used_variables
    

    def get_variable_count(self, term, variable):

        occurrences = 0
        
        for subterm in term:
            
            if isinstance(subterm, str):
                
                if subterm == variable:
                    
                    occurrences = occurrences + 1
            
            if isinstance(subterm, list):
            
                subterm_occurrences = self.get_variable_count( subterm, variable )
                occurrences = occurrences + subterm_occurrences
        
        return occurrences
            
            
    def get_nodes(self):
        
        return self.nodes
   
    
    def get_node_edges(self):
        
        return self.node_edges
    
    # Returns the term associated with the node identifier
    
    def get_term(self, node_label):
        
        for node in self.nodes:
            
            label, term, incoming_port_count = node
            
            if label == node_label:
                
                return term
            
                    
    def lambda_string_to_array(self, lambda_term):
            
        subterm = []
        array_lambda_term = []
        bracket_count = 0
        
        while len(lambda_term) != 0:
            
            if lambda_term[0] == "(":
            
                lambda_term = lambda_term[1:]
                bracket_count = bracket_count + 1
                
                while bracket_count != 0:

                    if lambda_term[0] == "(":
                        
                        bracket_count = bracket_count + 1
                        subterm.append(lambda_term[0])
                        lambda_term = lambda_term[1:]
                        
                        continue

                    elif lambda_term[0] == ")":
                        
                        bracket_count = bracket_count - 1
                        
                        if bracket_count != 0:
                            
                            subterm.append(lambda_term[0])
                        
                        lambda_term = lambda_term[1:]
                        
                        continue

                    elif lambda_term[0] == "λ":

                        subterm.append(lambda_term[0:2])
                        lambda_term = lambda_term[2:]
                        
                        continue
                    
                    elif lambda_term[0] == ".":
                        
                        lambda_term = lambda_term[1:]
                        
                        continue
                    
                    else:
                        
                        subterm.append(lambda_term[0])
                        lambda_term = lambda_term[1:]
                        
                        continue
                        
                array_lambda_term.append(subterm)
                subterm = []
                
            
            elif lambda_term[0] == "λ":

                array_lambda_term.append(lambda_term[0:2])
                lambda_term = lambda_term[2:]
                        
                continue
                    
            elif lambda_term[0] == ".":
                        
                lambda_term = lambda_term[1:]
                        
                continue
                    
            else:
                        
                array_lambda_term.append(lambda_term[0])
                lambda_term = lambda_term[1:]
                        
                continue

        return array_lambda_term
                    
                
    def remove_brackets(self, array_lambda_term):
        
        new_array_lambda_term = []
        new_subterm = []
        array_index = 0
        bracket_count = 0

        #This section only operates on array_lambda_term[array_index].
        #It repeteadly deletes this element.        

        while bracket_count == 0:
            
            if len(array_lambda_term) == 0:
                
                break
            
            if isinstance (array_lambda_term[0], list):
                
                new_subterm = self.remove_brackets(array_lambda_term[0])
                new_array_lambda_term.append(new_subterm)
                del array_lambda_term[0]
                new_subterm = []
                
                continue
                

            if isinstance (array_lambda_term[0], str):
                
                if array_lambda_term[0] == "(":
                    
                    bracket_count = bracket_count + 1
                    del array_lambda_term[0]
                    
                    while bracket_count != 0:
                        
                        if array_lambda_term[0] == "(":
                            
                            bracket_count = bracket_count + 1
                            
                            if bracket_count == 1:
                                
                                del array_lambda_term[0]
                                continue
                            
                            else:
                            
                                new_subterm.append(array_lambda_term[0])
                                array_lambda_term.remove(array_lambda_term[0])
                                continue
                        
                        elif array_lambda_term[array_index] == ")":
                            
                            bracket_count = bracket_count - 1
                            
                            if bracket_count == 0:
                                
                                del array_lambda_term[0]
                                continue
                            
                            else:

                                new_subterm.append(array_lambda_term[0])
                                del array_lambda_term[0]
                                continue
                            
                        else:
                            
                            new_subterm.append(array_lambda_term[0])
                            del array_lambda_term[0]
                            continue

                    new_array_lambda_term.append(new_subterm)
                    new_subterm = []
                    continue
                    


                else:

                    new_array_lambda_term.append(array_lambda_term[0])
                    del array_lambda_term[0]
        
        return new_array_lambda_term
                

    def check_for_brackets(self, lambda_array):
        
        for subterm in lambda_array:
            
            if isinstance (subterm, str):
                
                if subterm == "(":
                    
                    return True
                
                if subterm == ")":
                    
                    return True
                
            if isinstance (subterm, list):
                
                bracket_boolean = self.check_for_brackets(subterm)
                
                if bracket_boolean == True:
                    
                    return True
                
        return False

       
        
    def convert_lambda_string(self, lambda_string):
        
        lambda_array = self.lambda_string_to_array(lambda_string)
        bracket_boolean = self.check_for_brackets(lambda_array)
        
        while bracket_boolean == True:
            
            lambda_array = self.remove_brackets(lambda_array)
            bracket_boolean = self.check_for_brackets(lambda_array)
        
        return lambda_array
    
    
    def one_step_normal_form_subcombinator(self, original_node_identifier, lambda_array):  
        
        array_index = -1
        normalization_count = 0
        
        if len(lambda_array) <= 1:
            
            return normalization_count
        
        abstraction_boolean = True
        array_index = -1
        
        for subterm in lambda_array:
        
            array_index = array_index + 1
            
            if isinstance(subterm, str):
                
                if subterm[0] == 'λ':

                    abstraction_boolean = True
                    continue
                
                if subterm[0] != 'λ':
                    
                    abstraction_boolean = False
                    continue
                
            if isinstance(subterm, list):
                
                if abstraction_boolean == True:
                    
                    if isinstance(subterm[0], str):
                    
                        if subterm[0][0] == 'λ':
                            
                            new_variable_name = self.variable_list.pop()    
                            lifted_term = subterm        
                            lambda_array[array_index] = new_variable_name    
                            lifted_node_identifier = self.new_node(lifted_term)
                            normalization_count = normalization_count + 1
                            
                            self.new_edge(original_node_identifier, (new_variable_name, lifted_node_identifier))
                            
                            self.carry_over_edges(original_node_identifier, lambda_array, lifted_node_identifier, lifted_term)
                            
                            # self.print_graph(0)
                            
                            return normalization_count
                    
                        
                else:
                        
                    normalization_count = self.one_step_normal_form_subcombinator(original_node_identifier, subterm)
                    
                    if normalization_count > 0:
                        
                        # self.print_graph(0)
                        
                        return normalization_count
                    
                    else:
                        
                        abstraction_boolean = False
                        
                        continue
                
        return normalization_count
    
    
    def carry_over_edges(self, original_identifier, original_term, new_identifier, new_term):
        
        node_edge_index = -1  
        lifted_term_variables = self.get_used_variables(new_term)        
        original_term_variables = self.get_used_variables(original_term)
        
        for edge in self.node_edges:
           
           node_edge_index = node_edge_index + 1
           base_identifier = edge[0]
           
           if base_identifier == original_identifier:
               
               edges_left = True
   
               while edges_left == True:
               
                   edges_left = False 
               
                   connection_index = 0        
               
                   for connection in edge[1:]:
                       
                       connection_index = connection_index + 1
                       edge_variable, top_node_identifier = connection
                       
                       if edge_variable in lifted_term_variables:
                           
                           self.new_edge( new_identifier , (edge_variable, top_node_identifier ))
                           del self.node_edges[node_edge_index][connection_index]
                           
                           if len(self.node_edges[node_edge_index]) == 1:
                               
                               del self.node_edges[node_edge_index]

                           edges_left = True
                           
                           break 
        return
        
        
        
    
    def remove_used_variables(self, lambda_array):
        
        used_variables = self.get_used_variables(lambda_array)
        
        for variable in used_variables:
            
            if variable in self.variable_list:
            
                self.variable_list.remove(variable)
        
        
    
    def normal_form_subcombinator(self, lambda_term_string):
        
        original_array = self.convert_lambda_string(lambda_term_string)
        self.remove_used_variables(original_array)
        
        lifted_boolean, lifted_array = self.make_subcombinator_term( original_array )
        original_node_identifier = self.new_node(lifted_array)
        self.abstract_constants(original_node_identifier, lifted_array)
        
        reduction_count = 1
        normalization_step = -1
        
        while reduction_count != 0:
        
            reduction_count = 0  
        
            for node in self.nodes:
            
                node_identifier, node_term, number_edges = node    
                reductions = self.one_step_normal_form_subcombinator( node_identifier, node_term )
                reduction_count = reduction_count + reductions
                
                if reductions >= 1:
                    
                    normalization_step = normalization_step + 1
                    
                    self.print_graph(normalization_step)


    def abstract_constants(self, node_identifier, node_term):
            
        array_index = -1
        
        for subterm in node_term:
            
            array_index = array_index + 1
            
            if isinstance (subterm, str):
                
                if subterm in self.constants:
                    
                    new_variable = self.variable_list.pop()
                    node_term[ array_index ] = new_variable
                    new_node_identifier = self.new_node( subterm )
                    self.new_edge( node_identifier , (new_variable, new_node_identifier))
                    
            if isinstance (subterm, list):
                
                self.abstract_constants(node_identifier, subterm)
                        
      
    def make_subcombinator_term (self, lambda_array):
        
        lifted_boolean = False
        subterm_index = -1
        
        for subterm in lambda_array:
            
            subterm_index = subterm_index + 1
            
            if isinstance (subterm, list):
                
                lifted_boolean, subterm = self.make_subcombinator_term( subterm )
                
                if lifted_boolean == True:
                    
                    lifted_subterm = copy.deepcopy(subterm)
                    del lambda_array[subterm_index]
                    
                    for element in reversed(lifted_subterm):
                            
                        lambda_array.insert(subterm_index, element)
                
        lifted_boolean, lambda_array = self.lambda_lift( lambda_array)
        
        return lifted_boolean, lambda_array
        
    
    def lambda_lift(self, lambda_array):
        
        lifted_boolean = False
        
        if isinstance( lambda_array[0], list ):
            
            return lifted_boolean, lambda_array
        
        if isinstance (lambda_array[0], str):
            
            if lambda_array[0][0] != 'λ':
                
                return lifted_boolean, lambda_array
        
        bound_variables = self.get_bound_variables( lambda_array )
        free_variables = []
        variables = self.get_variables( lambda_array )
        
        for variable in variables:
            
            if variable not in bound_variables:
                
                if variable not in free_variables:
                    
                    if variable not in self.constants:
                
                        free_variables.append( variable )
                
        for free_variable in reversed(free_variables):
            
            new_abstraction = 'λ'+free_variable
            
            lambda_array.insert(0, new_abstraction)
         
        lifted_array = []
        lifted_array.append(lambda_array)
            
        for free_variable in free_variables:
            
            lifted_array.append(free_variable)
        
        lifted_boolean = True
        
        return lifted_boolean, lifted_array           
                
        
    def get_variables( self, lambda_array ):

        variables = []

        for subterm in lambda_array:
            
            if isinstance ( subterm, str ):
                
                if subterm[0] != 'λ':
                    
                    variables.append( subterm )  
                        
                        
            if isinstance ( subterm, list ):
                
                subterm_bound_variables = self.get_bound_variables( subterm )
                subterm_variables = self.get_variables( subterm)
                
                if subterm_variables != []:
                
                    for subterm_variable in subterm_variables:
                        
                        if subterm_variable not in subterm_bound_variables:
                        
                            variables.append( subterm_variable )
                        
        return variables
                    
                    
    def get_bound_variables( self, lambda_array):
        
        bound_variables = []
        
        for subterm in lambda_array:
            
            if isinstance(subterm, str):
                
                if subterm[0] == 'λ':
                    
                    bound_variables.append( subterm[1:] )
                    
                else:
                    
                    return bound_variables
        
    
    def lambda_lift_subterms(self, lambda_array, bound_variables):
        
        subterm_index = -1
        
        for subterm in lambda_array:
            
            if isinstance(subterm, str):
                
                if subterm[0] == 'λ':
                    
                    bound_variables.append( subterm[1:] )
                    
                else:
                    
                    break
        
        for subterm in lambda_array:
            
            subterm_index = subterm_index + 1
            
            if isinstance( subterm, list ):
            
                for subsubterm in subterm:
                
                    if isinstance(subsubterm, str):
                    
                        if subterm[0] == 'λ':
                        
                            bound_variables.append( subterm[1:] )
                        
                    else:
                        
                        break
                
                lambda_array[subterm_index] = self.lambda_lift(subterm, bound_variables)
                subsubterm_index = -1
                
                for subsubterm in subterm:
                
                    subsubterm_index = subsubterm_index + 1    
                
                    if isinstance (subsubterm, list):
                                            
                        for subsubterm in subterm:
                    
                            self.lambda_lift_subterms(subterm, bound_variables)
                            
                        else:
                        
                            continue
                        
                        lambda_array[subterm_index][subsubterm_index] = self.lambda_lift(subterm, bound_variables)
                
        lambda_array_string = self.lambda_array_to_string( lambda_array )
        
        return lambda_array
            
    
    
    def array_to_subcombinator_term(self, input_lambda_array):
        
        array_index = -1
        
        for subterm in input_lambda_array:
            
            lifitng_boolean = False
            array_index = array_index + 1
            
            if isinstance(subterm, str):
                
                continue
            
            elif isinstance(subterm, list):
                
                if isinstance(subterm[0], str):
                    
                    if subterm[0][0] == 'λ':
                        
                        subterm_copy = copy.deepcopy(subterm)
                        lifted_subterm = self.lambda_lift(subterm_copy)
                        del input_lambda_array[array_index]
                        
                        for element in reversed(lifted_subterm):
                            
                            input_lambda_array.insert(array_index, element)
                        
                        lifting_boolean = True
                        break
        
        final_output = self.lambda_lift(input_lambda_array)
        
        return final_output
                
                
    def subcombinator_to_lambda_string(self):
        
        substitute_boolean = True
        
        if len(self.node_edges) == 0:
            
            node_identifier, base_term, incoming_edges = self.nodes[0]
            
        else:
        
            while substitute_boolean == True:
            
                substitute_boolean = False     
            
                for edge in self.node_edges:
                    
                    base_node = edge[0]
                    base_term = self.get_term(base_node)
                        
                    for connection in edge[1:]:
                        
                        variable, top_node = connection
                        connecting_edges = False
                        
                        for edge_check in self.node_edges:
                            
                            base_edge_check = edge_check[0]
                            
                            if base_edge_check == top_node:
                                
                                connecting_edges = True
                                
                                continue
                            
                        if connecting_edges == False:
                            
                            top_term = self.get_term(top_node)
                            self.perform_substitution(base_term, top_term, top_node, variable)
                            substitute_boolean = True
                                
                            continue
                        
                        continue
            
        if len(self.nodes) == 1:
            
            node_identifier, node_term, incoming_edges = self.nodes[0]
            lambda_string = self.lambda_array_to_string(node_term)
            
        else:
            
            lambda_string = "More than one node left"
            
        return lambda_string
        
    
    def perform_substitution(self, original_term, substitute_term, top_node, variable):
        
        term_index = -1
        original_term_bound_variables = []
        
        for subterm in original_term:
            
            if isinstance(subterm, str):
                
                if subterm[0] == 'λ':
                    
                    original_term_bound_variables.append( subterm[1:] )
                    
                else:
                    
                    break
        
        if len(substitute_term) == 1:
                        
            if isinstance (substitute_term[0], str):
                            
                substitute_term = substitute_term[0]
        
        for subterm in original_term:
            
            term_index = term_index + 1
            
            if isinstance(subterm, str):
                
                if subterm == variable:
                    
                    if subterm not in original_term_bound_variables:
                    
                        original_term[term_index] = substitute_term
                        
                else:
                        
                    continue
                
            if isinstance(subterm, list):
                
                self.perform_substitution(subterm, substitute_term, top_node, variable)
                continue

        self.delete_node(top_node)
        node_edge_index = -1
    
        for node_edge in self.node_edges:
         
            node_edge_index = node_edge_index + 1
            edge_index = 0
         
            for edge in node_edge[1:]:
             
                edge_index = edge_index + 1
                port_label, top = edge
             
                if top == top_node:
                 
                    del self.node_edges[node_edge_index][edge_index]
                    
                    if len(self.node_edges[node_edge_index]) == 1:
                     
                        del self.node_edges[node_edge_index]        
        
        return
        
        
    def lambda_array_to_string(self, lambda_array):
        
        lambda_string = ""
        
        for element in lambda_array:
            
            if isinstance(element, str):
                
                if element[0] == 'λ':
                    
                    lambda_string = lambda_string+element+'.'
                    
                else:
                    
                    lambda_string = lambda_string+element
                    
                    
            elif isinstance(element, list):
                                
                if len(element) == 1:
                    
                    if isinstance (element[0], str):
                    
                        lambda_string = lambda_string+element[0]        
            
                lambda_string = lambda_string+'('
                subterm_string = self.lambda_array_to_string(element)
                lambda_string = lambda_string+subterm_string
                lambda_string = lambda_string+')'
                
        return lambda_string


class equivalent_lambda_term_subcombinator:
    
    def __init__ (self, nodes, node_edges):

        self.nodes = nodes
        self.node_edges = node_edges
        
    def subcombinator_to_lambda_string(self):
        
        substitute_boolean = True
        
        if len(self.node_edges) == 0:
            
            node_identifier, base_term, incoming_edges = self.nodes[0]
            
        else:
            while substitute_boolean == True:  
                
                substitute_boolean = False     
            
                for edge in self.node_edges:
                    
                    base_node = edge[0]
                    base_term = self.get_term(base_node)
                        
                    for connection in edge[1:]:
                        
                        variable, top_node = connection
                        connecting_edges = False
                        
                        for edge_check in self.node_edges:
                            
                            base_edge_check = edge_check[0]
        
                            if base_edge_check == top_node: 
                                
                                connecting_edges = True    
                                continue
                            
                        if connecting_edges == False:
                            
                            top_term = self.get_term(top_node)
                            self.perform_substitution(base_term, top_term, top_node, variable, [])
                            substitute_boolean = True
                            continue
                        
                        continue

        if len(self.nodes) == 1:
            node_identifier, node_term, incoming_edges = self.nodes[0]
            lambda_string = self.lambda_array_to_string(node_term)
            
        else:
            
            lambda_string = "More than one node left"
            
        return lambda_string
    
    
    def print_subcombinator_node_and_edge_arrays( self ):

        for node in self.nodes:
            print(node)
            
        print()
            
        for edge in self.node_edges:
            print(edge)
            
        return
        
        
    
    def perform_substitution(self, original_term, substitute_term, top_node, variable, original_bound_variables):
        
        bound_variables = []

        for bound_variable in original_bound_variables:
            
            bound_variables.append(bound_variable)
        
        term_index = -1
        
        for subterm in original_term:
            
            if isinstance(subterm, str):
                
                if subterm[0] == 'λ':
                    
                    bound_variables.append( subterm[1:] )
                    
                else:
                    
                    break
        
        if len(substitute_term) == 1:
                        
            if isinstance (substitute_term[0], str):
                            
                substitute_term = substitute_term[0]
        
        for subterm in original_term:
            
            term_index = term_index + 1
            
            if isinstance(subterm, str):
                
                if subterm == variable:
                    
                    if subterm not in bound_variables:
                    
                        original_term[term_index] = substitute_term

                else:
                        
                    continue
                
            if isinstance(subterm, list):
                
                self.perform_substitution(subterm, substitute_term, top_node, variable, bound_variables)
                continue

        self.delete_node(top_node)
        node_edge_index = -1
    
        for node_edge in self.node_edges:
         
            node_edge_index = node_edge_index + 1
            edge_index = 0
         
            for edge in node_edge[1:]:
             
                edge_index = edge_index + 1
                port_label, top = edge
             
                if top == top_node:
                 
                    del self.node_edges[node_edge_index][edge_index]

                    if len(self.node_edges[node_edge_index]) == 1:
                     
                        del self.node_edges[node_edge_index]   
                        
        return

    
    def get_variable_count( self, term, variable):
        
        variable_count = 0

        
        for subterm in term:
            
            if isinstance (subterm, str):
                
                if subterm == variable:
                    
                    variable_count = variable_count + 1
                    
                    continue
                    
                else:
                    
                    continue
                
            if isinstance (subterm, list):
                
                subterm_variable_count = self.get_variable_count( subterm, variable)
                
                # print("list")
                
                variable_count = variable_count + subterm_variable_count
                
                continue
                
        return variable_count
    
        
    def lambda_array_to_string(self, lambda_array):
        
        lambda_string = ""
        
        for element in lambda_array:
            
            if isinstance(element, str):
                
                if element[0] == 'λ':
                    
                    lambda_string = lambda_string+element+'.'
                    
                else:
                    
                    lambda_string = lambda_string+element
                    
            elif isinstance(element, list):
                                
                if len(element) == 1:
                    
                    if isinstance (element[0], str):
                    
                        lambda_string = lambda_string+element[0]        
            
                lambda_string = lambda_string+'('
                subterm_string = self.lambda_array_to_string(element)
                lambda_string = lambda_string+subterm_string
                lambda_string = lambda_string+')'

        return lambda_string
    

    def get_term(self, node_label):
        
        for node in self.nodes:
            
            label, term, incoming_port_count = node
            
            if label == node_label:
                
                return term
            
            
    def delete_node(self, identifier):
        
        node_index = -1
        
        for node in self.nodes:
            
            node_index = node_index + 1
            
            if node[0] == identifier:
                
                del self.nodes[node_index]
        
        node_edge_index = -1
        
        for node_edge in self.node_edges:
            
            node_edge_index = node_edge_index + 1
            
            if node_edge[0] == identifier:
                
                del self.node_edges[node_edge_index]    

        return

lambda_term_string = "(λf.λx.f(fx))(λf.λx.f(fx))S0"

church_numeral_22S0 = subcombinator( lambda_term_string )

church_numeral_22S0.run_steps( True )


test_input_string = "(λx.x)"

test = subcombinator( test_input_string )

convert_lambda_string_test1 = "(λf.λx.f(fx))(λf.λx.f(fx))S0"
print("convert_lambda_string_test1: "+str(test.convert_lambda_string(convert_lambda_string_test1 )))
print()

convert_lambda_string_test2 = "(λf.λx.f(fx))(λf.λx.(f(f(fx))))S0"
print("convert_lambda_string_test2: "+str(test.convert_lambda_string(convert_lambda_string_test2 )))
print()

convert_lambda_string_test3 = "(λb.λc.λa.λx.(λa.λc.λy.ac)acxb)bc"
print("convert_lambda_string_test2: "+str(test.convert_lambda_string(convert_lambda_string_test3 )))
print()

convert_lambda_string_test4 = "(λbc.bc)xy"
print("convert_lambda_string_test2: "+str(test.convert_lambda_string(convert_lambda_string_test4 )))
print()

print()

make_subcombinator_term_test1_string = "λa.λx.(λy.ac)xb"
make_subcombinator_term_test1_list = test.convert_lambda_string( make_subcombinator_term_test1_string )
print("make_subcombinator_term_test1: "+str( test.make_subcombinator_term( make_subcombinator_term_test1_list )))
print()

make_subcombinator_term_test2_string = "(λf.λx.f(S0))a(λf.λx.f(fx))"
make_subcombinator_term_test2_list = test.convert_lambda_string( make_subcombinator_term_test2_string )
print("make_subcombinator_term_test2: "+str( test.make_subcombinator_term( make_subcombinator_term_test2_list )))
print()

make_subcombinator_term_test3_string = "λa.λx.(λy.ac(λe.ee))xb"
make_subcombinator_term_test3_list = test.convert_lambda_string( make_subcombinator_term_test3_string )
print("make_subcombinator_term_test3: "+str( test.make_subcombinator_term( make_subcombinator_term_test3_list )))
print()

make_subcombinator_term_test4_string = "(λf.λx.f((λa.a)b))(λf.λx.f(fx))S0"
make_subcombinator_term_test4_list = test.convert_lambda_string( make_subcombinator_term_test4_string )
print("make_subcombinator_term_test4: "+str( test.make_subcombinator_term( make_subcombinator_term_test4_list )))
print()

print()

normal_form_subcombinator_test1 = subcombinator( "(λf.λx.f(fx))(λf.λx.f(fx))S0" )

make_subcombinator_term_test4_string = "(λf.λx.f((λa.a)b))(λf.λx.f(fx))S0"
print( make_subcombinator_term_test4_string )
make_subcombinator_term_test4_list = test.convert_lambda_string( make_subcombinator_term_test4_string )
print("make_subcombinator_term_test4: "+str( test.make_subcombinator_term( make_subcombinator_term_test4_list )))

normal_form_subcombinator_test2 = subcombinator( "(λf.λx.f((λa.a)b))(λf.λx.f(fx))S0" )



normal_form_subcombinator_test3 = subcombinator( "(λf.λx.f(fx))(λf.λx.f(fS))S0" )


normalize_test_string1 = "(λa.λx.(λy.ac)xb)SSS"
normalize_test1 = subcombinator ( normalize_test_string1 )
normalize_test1.run_steps( False )

normalize_test_string1 = "(λf.λx.f(f(fx)))(λf.λx.f(f(fx)))S0"
normalize_test1 = subcombinator ( normalize_test_string1 )
normalize_test1.run_steps( False )

normalize_test_string2 = "(λf.λx.f((λa.a)b))(λf.λx.f(fx))S0"
normalize_test2 = subcombinator ( normalize_test_string2 )
normalize_test2.run_steps( False )

normalize_test_string3 = "(λf.λx.f(fx))a(λf.λx.f(fx))bS0"
normalize_test3 = subcombinator ( normalize_test_string3 )
normalize_test3.run_steps( False )


normal_form_subcombinator_test1.run_steps( True )
            

# with open('check_potentials.txt', 'w') as f:
    
#     sys.stdout = f # Change the standard output to the file we created.

#     normal_form_subcombinator_test1.run_steps( True )
            
#     sys.stdout = original_stdout # Reset the standard output to its original value