-- Prove2me | solution 1 for Nock.NPR.fn_cons_dyck_constraint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:32:42.251182+00:00
-- url     : https://prove2.me/submissions/b8295c0a-edf5-405d-b73d-778e013bfd1e

module
public import Definitions.Def_LeanPool_PureNock_Dyck
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Data.List.GetD
public import Mathlib.Tactic.FieldSimp
public import Definitions.Def_LeanPool_PureNock_NPR
public import Theorems.Thm_Nock_NPR_fn_cons_dyck
public import Theorems.Thm_Nock_Noun_one_le_leaves


set_option autoImplicit true
@[expose] public section
public section
open Polynomial
open Nock
open Nock.NPR
variable {K : Type*} [Field K]
namespace Nock.NPR
theorem _root_.solution (l r : Noun) (x : K) :
    x * (fn (Noun.cell l r) x).2.2
      = x ^ 2 * (fn l x).2.2 + (fn l x).1 ^ 2 + x * (fn l x).1 ^ 2 * (fn r x).2.2 := by
  have hlam : 1 ≤ l.leaves := l.one_le_leaves
  have hsz : ((fn l x).1 : K) = x ^ l.leaves := rfl
  have hpow : x * x ^ (2 * l.leaves - 1) = (x ^ l.leaves) ^ 2 := by
    rw [← pow_mul, ← pow_succ']
    congr 1
    omega
  rw [fn_cons_dyck, hsz, mul_add, mul_add, hpow]
  ring
end Nock.NPR
