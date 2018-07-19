#Look for #IMPLEMENT tags in this file.

'''
Construct and return Kenken CSP model.
'''

from cspbase import *
import itertools
from functools import reduce
import operator

def kenken_csp_model(kenken_grid):
    '''Returns a CSP object representing a Kenken CSP problem along 
       with an array of variables for the problem. That is return

       kenken_csp, variable_array

       where kenken_csp is a csp representing the kenken model
       and variable_array is a list of lists

       [ [  ]
         [  ]
         .
         .
         .
         [  ] ]

       such that variable_array[i][j] is the Variable (object) that
       you built to represent the value to be placed in cell i,j of
       the board (indexed from (0,0) to (N-1,N-1))

       
       The input grid is specified as a list of lists. The first list
	   has a single element which is the size N; it represents the
	   dimension of the square board.
	   
	   Every other list represents a constraint a cage imposes by 
	   having the indexes of the cells in the cage (each cell being an 
	   integer out of 11,...,NN), followed by the target number and the
	   operator (the operator is also encoded as an integer with 0 being
	   '+', 1 being '-', 2 being '/' and 3 being '*'). If a list has two
	   elements, the first element represents a cell, and the second 
	   element is the value imposed to that cell. With this representation,
	   the input will look something like this:
	   
	   [[N],[cell_ij,...,cell_i'j',target_num,operator],...]
	   
       This routine returns a model which consists of a variable for
       each cell of the board, with domain equal to {1-N}.
       
       This model will also contain BINARY CONSTRAINTS OF NOT-EQUAL between
       all relevant variables (e.g., all pairs of variables in the
       same row, etc.) and an n-ary constraint for each cage in the grid.
    '''
    kenken_csp = CSP("kenken", [])
    dimension = kenken_grid[0][0]
    variable_domain = create_variable_domain(dimension)
    
    variable_array = create_variable_array(dimension, variable_domain)
    add_kenken_csp_variables(dimension, variable_array, kenken_csp)
    add_row_col_constraints(dimension, variable_domain, variable_array, kenken_csp)
    add_cage_constraints(kenken_grid, variable_array, kenken_csp)

    return kenken_csp, variable_array
      
    ##IMPLEMENT
    
def create_variable_domain(dimension):
    variable_domain = []
    for i in range(1, dimension + 1):
        variable_domain.append(i)
    return variable_domain

def create_variable_array(dimension, variable_domain):
    variable_array = []    
    for i in range(0, dimension):
        inside_list = []
        for j in range(0, dimension):
            var = Variable(str(i) + str(j), variable_domain)
            inside_list.append(var)
        variable_array.append(inside_list)       
    return variable_array

def add_kenken_csp_variables(dimension, variable_array, kenken_csp):
    for i in range(0, dimension):
        for j in range(0, dimension):
            kenken_csp.add_var(variable_array[i][j])

def add_row_col_constraints(dimension, variable_domain, variable_array, kenken_csp):
    perm_list = list(itertools.permutations(variable_domain, 2))
    comb_list = list(itertools.combinations(variable_domain, 2))
    for r in range(0, dimension):#row_constraints
        for i, j in comb_list:
            c = Constraint('r'+str(r)+' '+str(i-1)+str(j-1), [variable_array[r][i-1], variable_array[r][j-1]])
            c.add_satisfying_tuples(perm_list)
            kenken_csp.add_constraint(c)
            
    for r in range(0, dimension):#column_constraints
        for i, j in comb_list:
            c = Constraint('c'+str(r)+' '+str(i-1)+str(j-1), [variable_array[i-1][r], variable_array[j-1][r]])
            c.add_satisfying_tuples(perm_list)
            kenken_csp.add_constraint(c)
    
def split_int(ij):
    '''get the index of the variable in the variable_array'''
    return (ij // 10) - 1, (ij % 10) - 1

def subtract_from_left(lst):
    if len(lst) == 1:
        return lst[0]
    return subtract_from_left(lst[:len(lst) - 1]) - lst[len(lst) - 1]
    
def divide_from_left(lst):
    if len(lst) == 1:
        return lst[0]
    return divide_from_left(lst[:len(lst) - 1]) / lst[len(lst) - 1]
    
def add_cage_constraints(kenken_grid, variable_array, kenken_csp):
    dimension = kenken_grid[0][0]
    for index, b in enumerate(kenken_grid):
        if len(b) == 2:#two elements
            i,j = split_int(b[0])
            c = Constraint('cage'+str(index), [variable_array[i][j]])
            c.add_satisfying_tuples([[b[1]]])
            kenken_csp.add_constraint(c)
        else:
            cons_scope_list = []
            for ij_index in range(0, len(b) - 2):
                i,j = split_int(b[ij_index])
                cons_scope_list.append(variable_array[i][j])
            c = Constraint('cage'+str(index), cons_scope_list)
            n = len(cons_scope_list)               
            variable_domain = list(range(1,dimension + 1))
            satisfy_list = []
            if b[len(b) - 1] == 0:#add
                product_list = list(itertools.product(variable_domain, repeat=n))
                satisfy_list = []
                for t in product_list:
                    if sum(t) == b[len(b) - 2]:
                        satisfy_list.append(t)
                c.add_satisfying_tuples(satisfy_list)
                kenken_csp.add_constraint(c)
            elif b[len(b) - 1] == 1:#subtract
                #make a combination first and filter to get the valid lists, then do a permutation on it
                comb_list = list(itertools.combinations_with_replacement(variable_domain, n)) 
                satisfy_list = []                
                for l in comb_list:
                    l = list(l)#turn the tuple to list to make it easier to sort in decending order
                    l.sort(reverse=True)
                    if subtract_from_left(l) == b[len(b) - 2]:
                        perm_list = list(itertools.permutations(l, n))
                        for m in perm_list:
                            satisfy_list.append(m)
                c.add_satisfying_tuples(satisfy_list)
                kenken_csp.add_constraint(c)
            elif b[len(b) - 1] == 2:#divide
                comb_list = list(itertools.combinations_with_replacement(variable_domain, n)) 
                satisfy_list = []                
                for l in comb_list:
                    l = list(l)
                    l.sort(reverse=True)
                    if divide_from_left(l) == b[len(b) - 2]:
                        perm_list = list(itertools.permutations(l, n))
                        for m in perm_list:
                            satisfy_list.append(m)                
                c.add_satisfying_tuples(satisfy_list)
                kenken_csp.add_constraint(c)
            elif b[len(b) - 1] == 3:#multiply
                product_list = list(itertools.product(variable_domain, repeat=n))
                satisfy_list = []
                for t in product_list:
                    if reduce(operator.mul, t, 1) == b[len(b) - 2]:
                        satisfy_list.append(t)
                c.add_satisfying_tuples(satisfy_list)
                kenken_csp.add_constraint(c)