-- Prove2me | solution 1 for Nock.NPR.cpoly_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:29:48.520878+00:00
-- url     : https://prove2.me/submissions/1470fd41-c8ef-4a8b-9eba-dd4209bba82b

module
public import Definitions.Def_LeanPool_PureNock_Dyck
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Data.List.GetD
public import Mathlib.Tactic.FieldSimp
public import Definitions.Def_LeanPool_PureNock_NPR

set_option autoImplicit true
@[expose] public section
public section
open Polynomial
open Nock
open Nock.NPR
variable {K : Type*} [Field K]
namespace Nock.NPR
theorem _root_.solution (f g : ℕ → K) (n : ℕ) :
    cpoly f n - cpoly g n = cpoly (fun i => f i - g i) n := by
  unfold cpoly
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [← sub_mul, ← C_sub]
end Nock.NPR
