-- Prove2me | solution 1 for LongGapsBetweenPrimes.integerAverage_weight_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:59:51.952335+00:00
-- url     : https://prove2.me/submissions/871d2713-7492-4d34-b014-95c2570ed79f

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {ι : Type*} [Fintype ι] (T : ℕ) (c : ι → ℝ) (f : ι → ℕ → ℝ) :
    integerAverage T (fun n => (∑ i, c i * f i n) ^ 2) =
      ∑ i, ∑ j, c i * c j * integerAverage T (fun n => f i n * f j n) := by
  simp only [integerAverage, pow_two, Finset.sum_mul_sum, mul_mul_mul_comm]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := Finset.range T), ← Finset.mul_sum]
  simp only [Finset.sum_div, mul_div_assoc]
end LongGapsBetweenPrimes
