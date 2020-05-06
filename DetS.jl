

function divexact_mat(A::fmpz_mat, p::fmpz)
  for i=1:nrows(A)
    for j=1:ncols(A)
      A[i,j] = numerator(A[i,j]//p)
    end
  end
end


function NumDen(A::fmpq_mat)
n = nrows(A)
d = 1
    for i = 1: n
        d = lcm(d,denominator(A[i,1]))
    end
    AZ= matrix(ZZ,n,1,array_mat(d*A))   
    return AZ, d   
end


function array_mat(A::fmpz_mat)
   a = []
   for i=1:nrows(A)
     for j=1:ncols(A)
    push!(a, A[i,j])
     end
   end
return a
end


function array_mat(A::fmpq_mat)
   a = []
   for i=1:nrows(A)
     for j=1:ncols(A)
    push!(a, A[i,j])
     end
   end
return a
end


function rational_reconstruction_ZMat(A::fmpz_mat, M::fmpz)
  n = nrows(A)
  m = ncols(A)    
  B = zero_matrix(QQ,n,m)
  for i=1:n
    for j=1:m
      fl,a,b  = rational_reconstruction(A[i,j], M)
      B[i,j] = a//b
      if !fl 
        return false, B
      end
    end
  end
  return true, B
end



# Triangular denominator: for a solution matrix "s", given denominator d and A= d*s. 

function hcol(A::fmpz_mat, d::fmpz)
n = nrows(A)
w = deepcopy(A)
g = d
t = Array(ZZ,n)
h = zero_matrix(ZZ,n,n)
s = 1
v = 1
for i = 1:n
    k = n-(i-1)
    gg,e,f = gcdx(g,A[k,1])
    t[k] = f
    h[k,k] = numerator(g//gg)
    g = gg
end
  

for i = 1:n
    if h[i,i] == 1
        continue
    else
        for k = 1: i-1
            h[k,i] = mod(-t[i]*w[k,1], h[i,i])
            w[k,1] = mod(w[k,1]+h[k,i]*w[i,1], d)   
        end
        w[i,1] = h[i,i]*w[i,1]
        d = numerator(d//h[i,i])
        divexact_mat(w,h[i,i])
    end
end
    return h
end


# Triangular matrix using HNF
function hcol2(A::fmpz_mat, d::fmpz)
n = nrows(A)
w = deepcopy(A)
    D = matrix(ZZ,1,1,[d])
    S = vcat(D,A)
    O = zero_matrix(ZZ,1,n)
    I = MatrixSpace(ZZ,n,n)(1)
    OI= vcat(O,I)
    s = hcat(S,OI)
    H = hnf(s)
    return H[2:n+1,2:n+1]
end




#UniCert for integer matrices using Quadrstic lifting Storjohan
# k: # of steps
function UniCertZ(A::fmpz_mat, k::Int64)
n = nrows(A)
p = Hecke.next_prime(Hecke.p_start)
d = det(mod(A,fmpz(2)))
O = MatrixSpace(QQ,n,n)(0)

  if d==0
    return false
  else

  RR = ResidueRing(FlintZZ,p)
  W = MatrixSpace(RR,n,n)
  B = lift(inv(W(A)))
  AB = matrix(QQ,n,n,array_mat(A*B))
  I = MatrixSpace(QQ,n,n)(1)
  R = (I-AB)*(1//p)

        for i=0:k-1
            R = matrix(ZZ,n,n,array_mat(R))
            T = R^2
            M = lift(W(B*T))
            MM = matrix(QQ,n,n,array_mat(T-A*M))
            R = (MM)*(1//p) 

            if R==O
                return true
            else
                continue
            end
        end
            return false
   end
end



# Solver for fmpz matrices 

function DixonSol(A::fmpz_mat, B::fmpz_mat) 
p = next_prime(576567)#p_start)
println("mod") 
n = nrows(A) 
QA=matrix(QQ,n,n,array_mat(A))
QB=matrix(QQ,n,1,array_mat(B))
RR = ResidueRing(FlintZZ,p)
W = MatrixSpace(RR,n,n)
ap = lift(inv(W(A)))

println("Inv")
sol = 0*B
D = B
pp = fmpz(1)
last_SOL = false
nd = 0
    while true
    nd += 1
    y = ap*D
    mod!(y, fmpz(p))
    sol += y*pp
    pp *= p
    fl, SOL = rational_reconstruction_ZMat(sol, pp)
    if fl 

      if last_SOL == SOL && QA*SOL == QB
        println("used $nd $p-adic digits")
        return SOL
      else
        last_SOL = SOL
      end
    end
    D = D - A*y
    divexact_mat(D, fmpz(p))
#    if nbits(pp) > 10000 # a safety device to avoid infinite loops
#      error("not work")
#    end
  end
end




# Determinant algorithm: U is the range for random RHS matrx and k is #steps for Unicert. 

function DetS(A::fmpz_mat, U::AbstractArray, k::Int64)
n = ncols(A)
QA = matrix(QQ,n,n, array_mat(A))
b = rand(MatrixSpace(ZZ,n,1),U); 
Qb = matrix(QQ,n,1, array_mat(b)) 
#S = DixonSol(A, b)
S = solve(QA,Qb)
s , d1 =NumDen(S)
T = hcol(s, d1)
T = matrix(QQ,n,n, array_mat(T))
 
@time AT = QA*inv(T)

ZAT = matrix(ZZ,n,n, array_mat(AT))
fl = UniCertZ(ZAT,k)
    if fl
        return d1
    end


    while true
        b = rand(MatrixSpace(ZZ,n,1),U); 
        Qb = matrix(QQ,n,1, array_mat(b)) 
        S = solve(QA,Qb) 
#        S = DixonSol(A, b)
        TS = T*S
        s , d =NumDen(TS)
        T1 = hcol(s, d)  
        T1 = matrix(QQ,n,n, array_mat(T1))
        T = T1*T
        d1 *=d
@time        AT = AT*inv(T1) 
  
 
        ZAT = matrix(ZZ,n,n, array_mat(AT))
        fl = UniCertZ(ZAT,k)     
           
            if fl
                return d1
            end

    end

end




#= example

 A=rand(MatrixSpace(ZZ,10,10),1:10);
 DetS(A, 1:10,10)

 A=rand(MatrixSpace(ZZ,300,300),10:100);
 @time DetS(A, 10:100,10)


=#

