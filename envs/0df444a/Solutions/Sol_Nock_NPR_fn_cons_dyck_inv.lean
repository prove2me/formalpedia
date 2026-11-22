-- Prove2me | solution 1 for Nock.NPR.fn_cons_dyck_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:33:58.978039+00:00
-- url     : https://prove2.me/submissions/0e3fcb30-1dca-46fa-bfc7-0e3ca24622ba

module
public import Definitions.Def_LeanPool_PureNock_Dyck
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Data.List.GetD
public import Mathlib.Tactic.FieldSimp
public import Definitions.Def_LeanPool_PureNock_NPR
public import Theorems.Thm_Nock_NPR_fn_cons_dyck_constraint

set_option autoImplicit true
@[expose] public section
public section
open Polynomial
open Nock
open Nock.NPR
variable {K : Type*} [Field K]
namespace Nock.NPR
theorem _root_.solution (l r : Noun) {x : K} (hx : x ≠ 0) :
    (fn (Noun.cell l r) x).2.2
      = x * (fn l x).2.2 + (fn l x).1 ^ 2 * x⁻¹ + (fn l x).1 ^ 2 * (fn r x).2.2 := by
  have h := fn_cons_dyck_constraint l r x
  field_simp at h ⊢
  exact h
end Nock.NPR
