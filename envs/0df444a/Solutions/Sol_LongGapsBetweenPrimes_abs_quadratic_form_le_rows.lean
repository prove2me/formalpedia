-- Prove2me | solution 1 for LongGapsBetweenPrimes.abs_quadratic_form_le_rows
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:50:43.206616+00:00
-- url     : https://prove2.me/submissions/a3f7df75-dd9f-4c36-b722-06fa14125451

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (K : ι → ι → ℝ) (hK : ∀ i j, |K i j| = |K j i|) :
    |∑ i, ∑ j, c i * c j * K i j| ≤ ∑ i, c i ^ 2 * ∑ j, |K i j| := by
  calc
    |∑ i, ∑ j, c i * c j * K i j| ≤ ∑ i, ∑ j, |c i * c j * K i j| :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ j, (c i ^ 2 + c j ^ 2) / 2 * |K i j| := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_mul]
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      nlinarith [sq_nonneg (|c i| - |c j|), sq_abs (c i), sq_abs (c j)]
    _ = ∑ i, c i ^ 2 * ∑ j, |K i j| := by
      simp_rw [add_div, add_mul, Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun i j => c j ^ 2 / 2 * |K i j|)]
      simp_rw [← hK, ← Finset.mul_sum, ← Finset.sum_add_distrib, ← add_mul, add_halves]
end LongGapsBetweenPrimes
