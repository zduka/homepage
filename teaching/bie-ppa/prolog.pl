% =================================================================================================
% Helper functions - list membership
% =================================================================================================

%has(+E,+L)
% determines whether list L has element E in it
has(E, [E | _]).
has(E, [X | T]) :- 
    X \= E,
    has(E, T).

%hasnot(+E, +L)
% determines whether list L does not contain element E
hasnot(_, []).
hasnot(E, [X | T]) :- 
    X \= E, 
    hasnot(E, T).
    
% both functions: note that because the resuult is T or F, we are using the unification in prolog to return the value and therefore only provide termination conditions that should return T as facts, the F cases will not unify and therefore prolog will return F

% =================================================================================================
% Helper functions - list manipulation
% =================================================================================================

%reverseList(+L, -R)
% reverses the order of elements in L, the result is in R
reverseList(L, R) :- reverseList(L,R,[]).
reverseList([], ACC, ACC).
reverseList([H | T], R, ACC) :- reverseList(T, R, [ H | ACC]).

%prependList(+L, +L1, -R)
% prepends all elements from L to L1, returning the result in R
prependList([], L1, L1).
prependList([H | T], L1, R) :-
    prependList(T, L1, R2),
    R = [ H | R2].

%appendList(+L, +L1, -R)
% appends all elements from L to L1, returning the result in R
appendList(X,[],X).
appendList(X, [H | T], R) :-
    appendList(X, T, R2),
    R = [ H | R2].

% note that append(A,B,X) is equivalent to prepend(B,A,X)

% =================================================================================================
% Helper functions - graphs
% =================================================================================================

%neighbour(+G,+A,-B)
% given a graph and a node, returns neighbouring nodes, i.e. nodes B such that there is an edge from A to B. We first ignore the graph nodes since we are only using the edges and then walk all the edges and if we see edge from the node in question to some other node B, then node B is our neighbour.  

neighbour(g(_,E) ,A, B) :- neighbour2(E, A, B).
neighbour2([[A,B] | _ ], A, B).
neighbour2([ _ | T ], A, B) :- neighbour2(T,A,B).

% =================================================================================================
% Finding path from A to B
% =================================================================================================
    
%findPath(+G,+A,+B,-P)
% given graph G, finds a path from A to B and returns a list containing visited edges, for which we use an accumulator
findPath(G,A,B,P) :- findPath(G,A,B,P,[A]).

% if we are going to the same node we are now, we can stop and return the path so far
findPath(_,A,A, ACC, ACC).

% otherwise we must actually recurse, i.e. find a neighbour that we have not visited yet, add it to the path and try to find path from that neighbour to the end node
findPath(G,A,B,P,ACC) :- 
    neighbour(G, A, X), 
    hasnot(X, ACC), 
    findPath(G,X,B,P,[ X | ACC ]).

% =================================================================================================
% Graph Walking - Depth First Search
% =================================================================================================

%dfs(+G,+A,-R)
% The idea is to copy the basic algorithm of dfs, i.e. keep a stack of nodes to visit and process the stack one node at a time. We also drag the nodes visited so far in an accumulator and when the queue to process is empty, we return the accumulator. When a node is visited, we first check if the node has already been visited and if so, we continue to the next node. Otherwise we get all neighbours of the node and prepend them to the queue, add the node to the accumulator and continue processing the queue. 

% first convert the original query to the new one with stack being initialized to the starting node and accumulator to empty list
dfs(G,A, R) :- dfs(G, [A], [], R2), reverseList(R2, R).

% when there is nothing in the stack, return the accumulator
dfs(_, [], ACC, ACC).

% if the next element in the stack is already in the accumulator, skip it and proceed to the next element
dfs(G, [X | T], ACC, R) :-
    has(X, ACC), !,
    dfs(G, T, ACC, R).

% otherwise add the element to the accumulator, then add all neighbours of the node on the stack and call itself recursively on the new stack with the new accumulator
dfs(G, [X | T], ACC, R) :-
    ACC2 = [ X | ACC],
    findall(N , neighbour(G, X, N), ALL),
    prependList(ALL, T, Q),
    dfs(G, Q, ACC2, R).

% =================================================================================================
% Graph Walking - Breadth First Search
% =================================================================================================

% The idea of BFS is identical, but this time we use queue instead of stack, i.e. we append the neighbours instead of prependning them 
    
%bfs(+G,+A,-R)    
bfs(G, A, R) :- bfs(G, [A], [], R2), reverseList(R2, R).
bfs(_, [], ACC, ACC).
bfs(G, [X | T], ACC, R) :-
    has(X, ACC), !, 
    bfs(G, T, ACC, R).
bfs(G, [X | T], ACC, R) :-
    ACC2 = [X | ACC],
    findall(N, neighbour(G, X, N), ALL),
    appendList(ALL, T, Q), 
    bfs(G, Q, ACC2, R).

% =================================================================================================
% Speedier version 
% =================================================================================================

% greatest source of inefficiency is the fact that we always check the entire graph. We can however simply remove any edges leading to a node that is added to the queue, which means that there will be no way of actually getting to the node again. This would also make the graph smaller as we go, so even looking for neighbours will be faster. 

% to do this we start with the function removeEdgesTo, which removes from graph all edges leading to any of the nodes specified. 

%removeEdgesTo(+G, +A, -R)
% takes graph and removes all edges leading to all nodes in second argument (list of nodes). Returns the new graph in third

% first we extract the graph into edges only, do the magic and then reconstruct the graph back
removeEdgesTo(g(N,E), A, R) :- 
    removeEdgesTo2(E,A,R2), 
    R = g(N,R2).

% the magic: take next element from the list of nodes, remove all edges to it, and then recursively call itself on the changed graph with the rest of nodes 
removeEdgesTo2(E, [], E).
removeEdgesTo2(E, [H | T], R) :-
    removeEdgesToNode(E, H, E2),
    removeEdgesTo2(E2, T, R).

% this removes edges to a single node only 
removeEdgesToNode([], _, []).
removeEdgesToNode([[_, N] | T ], N, R) :- !, removeEdgesToNode(T, N, R).
removeEdgesToNode([ E | T], N, R) :-
    removeEdgesToNode(T, N, R2),
    R = [E | R2].

% now that we have the helper functions, we can do the fast dfs, the idea is the same as the original dfs, we keep the stack, however when we add node(s) to the stack, we remove all edges to them from the graph. This means we can skip the check whether a node has already been processed altogether:     
    
%fastDfs(+G,+A,-R)
fastDfs(G,A, R) :- 
    removeEdgesTo(G, [A], G2), 
    fastDfs(G2, [A], [], R2), 
    reverseList(R2, R).

% when there is nothing in the queue, return empty queue and the accumulator
fastDfs(_, [], ACC, ACC).

% otherwise add the element to the accumulator and then add the neighbours of the element to the queue
fastDfs(G, [X | T], ACC, R) :-
    ACC2 = [ X | ACC],
    findall(N , neighbour(G, X, N), ALL),
    prependList(ALL, T, Q),
    removeEdgesTo(G, ALL, G2),
    dfs(G2, Q, ACC2, R).

% =================================================================================================
% returning single node at a time
% =================================================================================================

% another interesting modification is changing the DFS algorithm so that we return one node at a time instead of the whole list at once, similarly to what neighbours do

%oneAtATimeDfs(+G,+A,-N)
oneAtATimeDfs(G,A, N) :- 
    removeEdgesTo(G, [A], G2), 
    oneAtATimeDfs2(G2, [A], N).

% the idea is simple, the termination condition is now whenever we take a node from the stack, we also return it
oneAtATimeDfs2(_, [A | _], A).

% when prolog continues, it tries the following rule on the same node, which then processes the node
oneAtATimeDfs2(G, [X | T], A) :-
    findall(N , neighbour(G, X, N), ALL),
    prependList(ALL, T, Q),
    removeEdgesTo(G, ALL, G2),
    oneAtATimeDfs2(G2, Q, A).
    
    
