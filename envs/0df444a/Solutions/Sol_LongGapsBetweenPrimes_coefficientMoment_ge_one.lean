-- Prove2me | solution 1 for LongGapsBetweenPrimes.coefficientMoment_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:29:42.056269+00:00
-- url     : https://prove2.me/submissions/e4bfdc72-e31b-4e67-baca-372eab57a258

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P : ℕ} (hP : P ≠ 0) (γ : ℝ) :
    1 ≤ coefficientMoment P γ := by
  have h := Finset.single_le_sum
    (f := fun d => coefficient P d ^ 2 * (d : ℝ) ^ γ / d.totient)
    (fun d _ => div_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (Nat.cast_nonneg _)) (Nat.one_mem_divisors.mpr hP)
  simpa [coefficientMoment, coefficient] using h
end LongGapsBetweenPrimes
