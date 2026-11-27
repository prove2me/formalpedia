-- Prove2me | solution 1 for MohP3.K.ntd_X_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:25:46.059647+00:00
-- url     : https://prove2.me/submissions/64f8f480-a7d3-41fe-8458-918043cad27e

module
public import Mathlib
public import Definitions.Def_MohP3_IndependenceK

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Polynomial
open MohP3 MohP3.K
variable (k : Type*) [Field k]
variable {k}
namespace MohP3.K
theorem _root_.solution (n : ℕ) (w : Polynomial k) (hw : w.coeff 0 ≠ 0) :
    ((X : Polynomial k) ^ n * w).natTrailingDegree = n := by
  have hw0 : w ≠ 0 := fun h => hw (by simp [h])
  rw [Polynomial.natTrailingDegree_mul (pow_ne_zero _ X_ne_zero) hw0,
    natTrailingDegree_X_pow, Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr hw), add_zero]
end MohP3.K
