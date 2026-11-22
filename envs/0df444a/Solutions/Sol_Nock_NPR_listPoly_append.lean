-- Prove2me | solution 1 for Nock.NPR.listPoly_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:30:55.788966+00:00
-- url     : https://prove2.me/submissions/707db9cd-252d-40cb-976d-7aa3bf9019ac

module
public import Definitions.Def_LeanPool_PureNock_Dyck
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Data.List.GetD
public import Mathlib.Tactic.FieldSimp
public import Definitions.Def_LeanPool_PureNock_NPR
public import Theorems.Thm_Nock_NPR_listPoly_nil
public import Theorems.Thm_Nock_NPR_listPoly_cons
attribute [local simp] Nock.NPR.listPoly_nil

set_option autoImplicit true
@[expose] public section
public section
open Polynomial
open Nock
open Nock.NPR
variable {K : Type*} [Field K]
namespace Nock.NPR
theorem _root_.solution (a b : List K) :
    listPoly (a ++ b) = listPoly a + X ^ a.length * listPoly b := by
  induction a with
  | nil => simp
  | cons x a' ih =>
      rw [List.cons_append, listPoly_cons, ih, listPoly_cons, List.length_cons, pow_succ]
      ring
end Nock.NPR
