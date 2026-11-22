-- Prove2me | solution 1 for LongGapsBetweenPrimes.coefficientMoment_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:53:05.041487+00:00
-- url     : https://prove2.me/submissions/af032fce-c1a1-478c-a3e4-e9ac4ac6504c

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_normalizer_pos
import Theorems.Thm_LongGapsBetweenPrimes_coefficientMoment_ge_one
import Theorems.Thm_LongGapsBetweenPrimes_coefficientMoment_sub_le
import Theorems.Thm_LongGapsBetweenPrimes_pow_le_mul_exp

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P : ℕ} (hP : 1 < P) {C γ : ℝ}
    (hC : 0 ≤ C) (hγ : 0 ≤ γ)
    (hM : coefficientAbsMoment P γ ≤ C * normalizer P) (k : ℕ) :
    coefficientMoment P γ ^ k ≤
      coefficientMoment P 0 ^ k * Real.exp ((k : ℝ) * C * γ) := by
  have hP0 : P ≠ 0 := by omega
  have hB := normalizer_pos hP
  have hbound : coefficientMoment P γ - coefficientMoment P 0 ≤ C * γ := by
    calc
      _ ≤ γ / normalizer P * coefficientAbsMoment P γ := coefficientMoment_sub_le hP γ
      _ ≤ γ / normalizer P * (C * normalizer P) :=
        mul_le_mul_of_nonneg_left hM (div_nonneg hγ hB.le)
      _ = C * γ := by field_simp
  simpa [mul_assoc] using pow_le_mul_exp (coefficientMoment_ge_one hP0 0)
    (zero_le_one.trans (coefficientMoment_ge_one hP0 γ)) (mul_nonneg hC hγ)
    (by linarith : coefficientMoment P γ ≤ coefficientMoment P 0 + C * γ) k
end LongGapsBetweenPrimes
