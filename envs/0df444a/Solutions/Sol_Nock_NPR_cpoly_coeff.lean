-- Prove2me | solution 1 for Nock.NPR.cpoly_coeff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:09:44.868276+00:00
-- url     : https://prove2.me/submissions/ff9cc634-649b-43f4-b7ba-57b445bfc293

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
theorem _root_.solution (f : ℕ → K) (n j : ℕ) :
    (cpoly f n).coeff j = if j < n then f j else 0 := by
  unfold cpoly
  rw [finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq (Finset.range n) j f]
  simp [Finset.mem_range]
end Nock.NPR
