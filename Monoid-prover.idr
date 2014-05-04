module MonoidProver

------------------------------------------------------------------------
-- Monoid expressions

-- There is one constructor for every operation, plus one for
-- variables; there may be at most n variables.

infixl 5 :+:

data Expr : Nat -> Type where
  Var  : Fin n -> Expr n
  Id   : Expr n
  (:+:) : Expr n -> Expr n -> Expr n

Env : VerifiedMonoid a => (a : Type) -> Nat -> Type
Env A n = Vect n A

-- The semantics of an expression is a function from an environment to
-- a value.


total

eval : VerifiedMonoid a => Expr n -> Env a n -> a
eval (Var i) env    = index i env
eval Id      env    = neutral
eval (e :+: e') env = eval e env <+> eval e' env

------------------------------------------------------------------------
-- Normal forms

-- A normal form is a list of variables.

Normal : Nat -> Type
Normal n = List (Fin n)

total 

evalNormal : VerifiedMonoid a => Normal n -> Env a n -> a
evalNormal [ ]       env = neutral
evalNormal (n :: ns) env = index n env <+> evalNormal ns env

-- a normalizer

total

normalize : Expr n -> Normal n
normalize (Var i)    = [ i ]
normalize Id         = [ ]
normalize (e :+: e') = normalize e ++ normalize e'

-- normalize is homomorphic with respect to ++ and <+>

homomorphic : (VerifiedMonoid a, VerifiedSemigroup a) => (nf1 : Normal n) -> (nf2 : Normal n) -> (env : Env a n) ->
              evalNormal (nf1 ++ nf2) env = evalNormal nf1 env <+> evalNormal nf2 env
homomorphic [ ] nf2 env = ?homomorphic0
homomorphic (n :: ns) nf2 env with (homomorphic ns nf2 env)
   | p with (semigroupOpIsAssociative (index n env) (evalNormal ns env) (evalNormal nf2 env))                 
            | x = ?homomorphic1
                                      

---------- Proofs ----------

MonoidProver.homomorphic0 = proof
  intros
  rewrite (monoidNeutralIsNeutralR (evalNormal nf2 env))
  refine refl


{-MonoidProver.homomorphic1 = proof
  intros
  rewrite sym p
  refine semigroupOpIsAssociative
  trivial
  exact (index n1 env)
  exact (evalNormal ns env)
  exact (evalNormal nf2 env) -}
