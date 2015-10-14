module LiftedHierarchies

using JuMP, Iterators

export lovasz_schrijver, lovasz_schrijver_plus, sherali_adams

lovasz_schrijver(m::Model) = lovasz_schrijver!(copy(m))

function lovasz_schrijver!(m::Model)
    var_idx  = 1:m.numCols
    bin_idx  = filter(x -> (m.colCat[x] == :Bin),  var_idx)
    cont_idx = filter(x -> (m.colCat[x] == :Cont), var_idx)
    variables  = [Variable(m,i) for i in var_idx]
    binaries   = [Variable(m,i) for i in  bin_idx]
    continuous = [Variable(m,i) for i in cont_idx]

    isempty(bin_idx) && return m

    old_linconstr = copy(m.linconstr)
    empty!(m.linconstr)

    for y in binaries
        for con in old_linconstr
            if con.lb != -Inf
                @addConstraint(m,    y *(con.terms - con.lb) ≥ 0)
                @addConstraint(m, (1-y)*(con.terms - con.lb) ≥ 0)
            end
            if con.ub != Inf
                @addConstraint(m,    y *(con.ub - con.terms) ≥ 0)
                @addConstraint(m, (1-y)*(con.ub - con.terms) ≥ 0)
            end
        end
        for i in 1:m.numCols
            lb, ub = m.colLower[i], m.colUpper[i]
            if lb != -Inf
                @addConstraint(m,    y *(variables[i] - lb) ≥ 0)
                @addConstraint(m, (1-y)*(variables[i] - lb) ≥ 0)
            end
            if ub != Inf
                @addConstraint(m,    y *(ub - variables[i]) ≥ 0)
                @addConstraint(m, (1-y)*(ub - variables[i]) ≥ 0)
            end
        end
    end

    # every constraint should be quadratic, else we have some constraint w/o any variables
    @assert isempty(m.linconstr)

    y = Dict()
    for b in binaries, v in variables
        if b == v
            y[b,v] = b
        elseif haskey(y, (v,b))
            y[b,v] = y[v,b]
        else
            y[b,v] = @defVar(m, lin)
        end
    end
    for q in m.quadconstr
        sign = (q.sense == :(>=)) ? 1 : -1
        term = q.terms
        aff = term.aff
        for idx in 1:length(term.qvars1)
            qv1, qv2 = term.qvars1[idx], term.qvars2[idx]
            coef = term.qcoeffs[idx]
            aff += coef * y[qv1,qv2]
        end
        @addConstraint(m, sign*aff ≥ 0)
    end

    empty!(m.quadconstr)
    # fill!(m.colCat, :Cont)

    m
end

lovasz_schrijver_plus(m::Model) = lovasz_schrijver_plus!(copy(m))

function lovasz_schrijver_plus!(m::Model)
    var_idx  = 1:m.numCols
    bin_idx  = filter(x -> (m.colCat[x] == :Bin),  var_idx)
    cont_idx = filter(x -> (m.colCat[x] == :Cont), var_idx)
    variables  = [Variable(m,i) for i in var_idx]
    binaries   = [Variable(m,i) for i in  bin_idx]
    continuous = [Variable(m,i) for i in cont_idx]

    isempty(bin_idx) && return m

    old_linconstr = copy(m.linconstr)
    empty!(m.linconstr)

    for y in binaries
        for con in old_linconstr
            if con.lb != -Inf
                @addConstraint(m,    y *(con.terms - con.lb) ≥ 0)
                @addConstraint(m, (1-y)*(con.terms - con.lb) ≥ 0)
            end
            if con.ub != Inf
                @addConstraint(m,    y *(con.ub - con.terms) ≥ 0)
                @addConstraint(m, (1-y)*(con.ub - con.terms) ≥ 0)
            end
        end
        for i in 1:m.numCols
            lb, ub = m.colLower[i], m.colUpper[i]
            if lb != -Inf
                @addConstraint(m,    y *(variables[i] - lb) ≥ 0)
                @addConstraint(m, (1-y)*(variables[i] - lb) ≥ 0)
            end
            if ub != Inf
                @addConstraint(m,    y *(ub - variables[i]) ≥ 0)
                @addConstraint(m, (1-y)*(ub - variables[i]) ≥ 0)
            end
        end
    end

    # every constraint should be quadratic, else we have some constraint w/o any variables
    @assert isempty(m.linconstr)

    y = Dict()
    for b in binaries, v in variables
        if b == v
            y[b,v] = b
        elseif haskey(y, (v,b))
            y[b,v] = y[v,b]
        else
            y[b,v] = @defVar(m, lin)
        end
    end
    for q in m.quadconstr
        sign = (q.sense == :(>=)) ? 1 : -1
        term = q.terms
        aff = term.aff
        for idx in 1:length(term.qvars1)
            qv1, qv2 = term.qvars1[idx], term.qvars2[idx]
            coef = term.qcoeffs[idx]
            aff += coef * y[qv1,qv2]
        end
        @addConstraint(m, sign*aff ≥ 0)
    end

    empty!(m.quadconstr)
    # fill!(m.colCat, :Cont)

    Y = Array(AffExpr, length(bin_idx)+1, length(bin_idx)+1)
    Y[1,1] = 1
    for (i,b) in enumerate(binaries)
        Y[1,i+1] = b
        Y[i+1,1] = b
        for (j,c) in enumerate(binaries)
            Y[i+1,j+1] = y[b,c]
        end
    end
    @addSDPConstraint(m, Y ≥ 0)

    m
end

sherali_adams(m::Model, level::Int) = sherali_adams!(copy(m), level)

function sherali_adams!(m::Model, level::Int)
    var_idx  = 1:m.numCols
    bin_idx  = filter(x -> (m.colCat[x] == :Bin),  var_idx)
    cont_idx = filter(x -> (m.colCat[x] == :Cont), var_idx)
    variables  = [Variable(m,i) for i in var_idx]
    binaries   = [Variable(m,i) for i in  bin_idx]
    continuous = [Variable(m,i) for i in cont_idx]

    # @assert union(cont_idx,bin_idx) == var_idx

    isempty(bin_idx) && return m

    old_linconstr = copy(m.linconstr)
    empty!(m.linconstr)

    sets = Any[]
    for k in 0:level
        for sset in subsets(bin_idx,k)
            push!(sets, sset)
            for ci in cont_idx
                push!(sets, sort([sset;ci]))
            end
        end
    end
    for sset in subsets(bin_idx,level+1)
        push!(sets, sset)
    end

    @defVar(m, Y[sets])

    for i in var_idx
        @addConstraint(m, Y[[i]] == Variable(m,i))
    end

    for k in 1:min(level,length(bin_idx)), I in subsets(bin_idx, k)
        for S in subsets(I)
            T = setdiff(I, S)
            for con in old_linconstr
                if con.lb != -Inf
                    @addConstraint(m, sum{ (-1)^(length(T′)) *
                                          (sum{ aᵢ * Y[sort!(union(S,T′,vᵢ.col))], (aᵢ,vᵢ) in zip(con.terms.coeffs,con.terms.vars)} -
                                          con.lb * Y[sort!(union(S,T′))]),
                                          k in 0:length(T), T′ in combinations(T,k)} ≥ 0)
                end
                if con.ub != Inf
                    @addConstraint(m, sum{ (-1)^(length(T′)) *
                                          (sum{ aᵢ * Y[sort!(union(S,T′,vᵢ.col))], (aᵢ,vᵢ) in zip(con.terms.coeffs,con.terms.vars)} -
                                          con.ub * Y[sort!(union(S,T′))]),
                                          k in 0:length(T), T′ in combinations(T,k)} ≤ 0)
                end
            end
            for i in var_idx
                lb, ub = m.colLower[i], m.colUpper[i]
                if lb != -Inf
                    @addConstraint(m, sum{ (-1)^(length(T′)) *
                                          (Y[sort!(union(S,T′,i))] -
                                          lb * Y[sort!(union(S,T′))]),
                                          k in 0:length(T), T′ in combinations(T,k)} ≥ 0)
                end
                if ub != Inf
                    @addConstraint(m, sum{ (-1)^(length(T′)) *
                                          (Y[sort!(union(S,T′,i))] -
                                          ub * Y[sort!(union(S,T′))]),
                                          k in 0:length(T), T′ in combinations(T,k)} ≤ 0)
                end
            end
        end
    end

    m
end

end # module
