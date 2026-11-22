-- Prove2me | solution 1 for Nock.NPR.listPoly_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:30:30.111796+00:00
-- url     : https://prove2.me/submissions/2298fc2a-ae21-46ff-8e83-29a2625ffb72

module
public import Definitions.Def_LeanPool_PureNock_Dyck
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Data.List.GetD
public import Mathlib.Tactic.FieldSimp
public import Definitions.Def_LeanPool_PureNock_NPR
public import Theorems.Thm_Nock_NPR_listPoly_coeff
public import Theorems.Thm_Nock_NPR_listPoly_nil
attribute [local simp] Nock.NPR.listPoly_nil

set_option autoImplicit true
@[expose] public section
public section
open Polynomial
open Nock
open Nock.NPR
variable {K : Type*} [Field K]
namespace Nock.NPR
theorem _root_.solution (x : K) (l : List K) :
    listPoly (x :: l) = C x + X * listPoly l := by
  ext j
  rw [coeff_add, listPoly_coeff]
  match j with
  | 0 =>
      rw [mul_coeff_zero, coeff_X_zero, zero_mul, add_zero, coeff_C_zero,
        List.getD_cons_zero]
      simp
  | k + 1 =>
      rw [coeff_X_mul, listPoly_coeff, coeff_C, List.getD_cons_succ, List.length_cons]
      simp
end Nock.NPR
