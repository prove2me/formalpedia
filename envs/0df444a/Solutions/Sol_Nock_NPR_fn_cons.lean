-- Prove2me | solution 1 for Nock.NPR.fn_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:33:56.043814+00:00
-- url     : https://prove2.me/submissions/a205307d-9e08-475c-ac27-84a48a15125b

module
public import Definitions.Def_LeanPool_PureNock_Dyck
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Data.List.GetD
public import Mathlib.Tactic.FieldSimp
public import Definitions.Def_LeanPool_PureNock_NPR
public import Theorems.Thm_Nock_NPR_fn_cons_size
public import Theorems.Thm_Nock_NPR_fn_cons_leaf
public import Theorems.Thm_Nock_NPR_fn_cons_dyck

set_option autoImplicit true
@[expose] public section
public section
open Polynomial
open Nock
open Nock.NPR
variable {K : Type*} [Field K]
namespace Nock.NPR
theorem _root_.solution (l r : Noun) (x : K) :
    fn (Noun.cell l r) x
      = ( (fn l x).1 * (fn r x).1
        , (fn l x).2.1 + (fn l x).1 * (fn r x).2.1
        , x * (fn l x).2.2 + x ^ (2 * l.leaves - 1)
            + x ^ (2 * l.leaves) * (fn r x).2.2 ) :=
  Prod.ext_iff.mpr ⟨fn_cons_size l r x,
    Prod.ext_iff.mpr ⟨fn_cons_leaf l r x, fn_cons_dyck l r x⟩⟩
end Nock.NPR
