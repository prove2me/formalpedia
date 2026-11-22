-- Prove2me | solution 1 for LongGapsBetweenPrimes.sum_tupleMass_mul_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:37:01.442814+00:00
-- url     : https://prove2.me/submissions/79bc3b8c-1c4e-448e-854c-859ca7105ebe

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_sum_divisorIndex

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution (P k : ℕ) (γ : ℝ) :
    (∑ r : DivisorTuple P k, tupleMass r * (tupleProduct r : ℝ) ^ γ) =
      coefficientMoment P γ ^ k := by
  classical
  unfold tupleMass tupleProduct
  simp_rw [Nat.cast_prod,
    ← Real.finsetProd_rpow _ _ (fun _ _ => Nat.cast_nonneg _),
    ← Finset.prod_mul_distrib, div_mul_eq_mul_div]
  rw [← Fintype.prod_sum (fun (_ : Fin k) (d : DivisorIndex P) =>
    coefficient P d.val ^ 2 * (d.val : ℝ) ^ γ / (d.val.totient : ℝ))]
  rw [sum_divisorIndex P (fun d => coefficient P d ^ 2 * (d : ℝ) ^ γ / d.totient)]
  simp [coefficientMoment]
end LongGapsBetweenPrimes
