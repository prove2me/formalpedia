-- Prove2me | solution 1 for MohP3.ntd_X_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:45:21.146556+00:00
-- url     : https://prove2.me/submissions/301cc019-946a-4b3c-aea7-770201d747d4

module
public import Mathlib
public import Definitions.Def_MohP3_Independence

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Polynomial
open MohP3
namespace MohP3
theorem _root_.solution (n : ℕ) (w : ℚ[X]) (hw : w.coeff 0 ≠ 0) :
    ((X:ℚ[X])^n * w).natTrailingDegree = n := by
  have hw0 : w ≠ 0 := fun h => hw (by simp [h])
  rw [Polynomial.natTrailingDegree_mul (pow_ne_zero _ X_ne_zero) hw0,
    natTrailingDegree_X_pow, Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr hw), add_zero]
end MohP3
