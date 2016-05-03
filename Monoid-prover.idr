module MonoidProver

import Classes.Verified

import Data.Fin
import Data.Vect 
import Syntax.PreorderReasoning

%default total

------------------------------------------------------------------------
-- Monoid expressions

-- There is one constructor for every operation, plus one for
-- variables; there may be at most n variables.

infixl 5 :+:

data Expr : Nat -> Type where
  Var  : Fin n -> Expr n
  Id   : Expr n
  (:+:) : Expr n -> Expr n -> Expr n

Env : (a : Type) -> Nat -> Type
Env a n = Vect n a

-- The semantics of an expression is a function from an environment to
-- a value.

eval : VerifiedMonoid a => Expr n -> Env a n -> a
eval (Var i) env    = index i env
eval Id      env    = neutral
eval (e :+: e') env = eval e env <+> eval e' env

------------------------------------------------------------------------
-- Normal forms

-- A normal form is a list of variables.

Normal : Nat -> Type
Normal n = List (Fin n) 

evalNormal : VerifiedMonoid a => Normal n -> Env a n -> a
evalNormal [ ]       env = neutral
evalNormal (n :: ns) env = index n env <+> evalNormal ns env

-- a normalizer

normalize : Expr n -> Normal n
normalize (Var i)    = [ i ]
normalize Id         = [ ]
normalize (e :+: e') = normalize e ++ normalize e'

-- normalize is homomorphic with respect to ++ and <+>

homomorphic : VerifiedMonoid a => (nf1 : Normal n) -> 
                                  (nf2 : Normal n) -> 
                                  (env : Env a n) -> 
              evalNormal (nf1 ++ nf2) env = (evalNormal nf1 env) <+> (evalNormal nf2 env)
homomorphic [] nf2 env = 
            (evalNormal ([] ++ nf2) env)     ={ Refl }=
            (evalNormal nf2 env)             ={ sym  (monoidNeutralIsNeutralR 
                                                          (evalNormal nf2 env)) }=
            (neutral <+> evalNormal nf2 env) ={ Refl }=
            (evalNormal [] env <+> evalNormal nf2 env)
            QED
homomorphic (n :: nf1) nf2 env = 
            ((index n env) <+> (evalNormal (nf1 ++ nf2) env))  
                    ={ cong (homomorphic nf1 nf2 env) }=
            ((index n env) <+> (evalNormal nf1 env <+> evalNormal nf2 env)) 
                    ={ semigroupOpIsAssociative (index n env) (evalNormal nf1 env) 
                                                              (evalNormal nf2 env) }=
            (((index n env) <+> (evalNormal nf1 env)) <+> evalNormal nf2 env) ={ Refl }=
            ((evalNormal (n :: nf1) env) <+> evalNormal nf2 env)
            QED

-- normalize is correct

cong2 : {A : Type} ->
        {B : Type} ->
        {C : Type} ->
        {x : A}    ->
        {z : A}    ->
        {y : B}    ->
        {w : B}    ->
        {f : A -> B -> C} ->
        (x = z) ->
        (y = w) ->
        f x y = f z w
cong2 Refl Refl = Refl        

normalizeSound : VerifiedMonoid a => (e : Expr n) -> 
                                     (env : Env a n) -> 
                                     evalNormal (normalize e) env = eval e env
normalizeSound (Var x) env 
    = (evalNormal (normalize (Var x)) env) ={ Refl }= 
      (evalNormal [ x ] env)               ={ Refl }=
      (index x env <+> evalNormal [] env)  ={ Refl }=
      (index x env <+> neutral)            ={ monoidNeutralIsNeutralL (index x env) }=
      (index x env)
      QED
normalizeSound Id env = Refl
normalizeSound (x :+: y) env 
    = (evalNormal ((normalize x) ++ (normalize y)) env) 
           ={ homomorphic (normalize x) (normalize y) env }=
      ((evalNormal (normalize x) env) <+> (evalNormal (normalize y) env)) 
           ={ cong2 (normalizeSound x env) (normalizeSound y env) }= 
      ((eval x env) <+> (eval y env))
      QED

-- Local Variables:
-- idris-packages: ("contrib")
-- End:
