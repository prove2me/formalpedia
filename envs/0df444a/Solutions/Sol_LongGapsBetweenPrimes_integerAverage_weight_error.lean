-- Prove2me | solution 1 for LongGapsBetweenPrimes.integerAverage_weight_error
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:01:21.63589+00:00
-- url     : https://prove2.me/submissions/7c394754-ea94-44aa-80ee-598a138aba30

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_integerAverage_weight_sq

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {ι : Type*} [Fintype ι] (q T : ℕ)
    (c : ι → ℝ) (hc : ∀ i, |c i| ≤ 1) (f : ι → ℕ → ℝ) (E : ℝ)
    (hpair : ∀ i j, |integerAverage T (fun n => f i n * f j n) -
      integerAverage q (fun n => f i n * f j n)| ≤ E) :
    |integerAverage T (fun n => (∑ i, c i * f i n) ^ 2) -
      integerAverage q (fun n => (∑ i, c i * f i n) ^ 2)| ≤ (Fintype.card ι : ℝ) ^ 2 * E := by
  simp only [integerAverage_weight_sq, ← Finset.sum_sub_distrib, ← mul_sub]
  calc
    _ ≤ ∑ i, ∑ j, E := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      apply Finset.sum_le_sum
      intro i _
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_mul]
      calc
        _ ≤ 1 * 1 * |integerAverage T (fun n => f i n * f j n) -
            integerAverage q (fun n => f i n * f j n)| := by
          gcongr <;> apply hc
        _ ≤ E := by simpa using hpair i j
    _ = _ := by simp [pow_two, mul_assoc]
end LongGapsBetweenPrimes
