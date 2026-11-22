-- Prove2me | solution 1 for LongGapsBetweenPrimes.coefficientAbsMoment_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:56:16.647609+00:00
-- url     : https://prove2.me/submissions/80426f90-4a1d-492d-a3cc-fa4ac4fefce3

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_one_lt_of_mem_divisors_erase_one
import Theorems.Thm_LongGapsBetweenPrimes_normalizer_pos
import Theorems.Thm_LongGapsBetweenPrimes_coefficientAbsMoment_zero
import Theorems.Thm_LongGapsBetweenPrimes_abs_coefficient_eq

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {P Y : ℕ} (hP : 1 < P) (hY : 1 < Y)
    {γ E : ℝ} (hγ : 0 ≤ γ) (hYE : (Y : ℝ) ^ γ ≤ E) :
    coefficientAbsMoment P γ ≤ E + divisorEulerMoment P γ / (normalizer P * Real.log Y) := by
  have hB : 0 < normalizer P := normalizer_pos hP
  have hlogY : 0 < Real.log (Y : ℝ) := Real.log_pos (by exact_mod_cast hY)
  have hden : 0 < normalizer P * Real.log Y := mul_pos hB hlogY
  have hE : 0 ≤ E := (Real.rpow_nonneg (Nat.cast_nonneg _) _).trans hYE
  have hpoint (d : ℕ) (hd : d ∈ P.divisors.erase 1) :
      |coefficient P d| * (d : ℝ) ^ γ / d.totient ≤
        E * (|coefficient P d| / d.totient) +
          (1 / (normalizer P * Real.log Y)) * ((d : ℝ) ^ γ / d.totient) := by
    have hd1 := one_lt_of_mem_divisors_erase_one hd
    have hf : 0 ≤ |coefficient P d| / (d.totient : ℝ) :=
      div_nonneg (abs_nonneg _) (Nat.cast_nonneg _)
    have hg : 0 ≤ (d : ℝ) ^ γ / d.totient :=
      div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg _)
    by_cases hdY : d ≤ Y
    · have hpow : (d : ℝ) ^ γ ≤ E :=
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hdY) hγ).trans hYE
      calc
        _ = (|coefficient P d| / d.totient) * (d : ℝ) ^ γ := by ring
        _ ≤ (|coefficient P d| / d.totient) * E := mul_le_mul_of_nonneg_left hpow hf
        _ ≤ _ := by nlinarith [mul_nonneg (one_div_nonneg.mpr hden.le) hg]
    · have hac : |coefficient P d| ≤ 1 / (normalizer P * Real.log Y) := by
        rw [abs_coefficient_eq hP hd1]
        apply one_div_le_one_div_of_le hden
        exact mul_le_mul_of_nonneg_left
          (Real.log_le_log (by exact_mod_cast (by omega : 0 < Y))
            (by exact_mod_cast (by omega : Y ≤ d))) hB.le
      calc
        _ = |coefficient P d| * ((d : ℝ) ^ γ / d.totient) := by ring
        _ ≤ (1 / (normalizer P * Real.log Y)) * ((d : ℝ) ^ γ / d.totient) :=
          mul_le_mul_of_nonneg_right hac hg
        _ ≤ _ := by nlinarith [mul_nonneg hE hf]
  have hsmall : (∑ d ∈ P.divisors.erase 1, |coefficient P d| / d.totient) = 1 := by
    simpa [coefficientAbsMoment] using coefficientAbsMoment_zero hP
  have hlarge : (∑ d ∈ P.divisors.erase 1, (d : ℝ) ^ γ / d.totient) ≤ divisorEulerMoment P γ :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      (fun d _ _ => div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg _))
  calc
    coefficientAbsMoment P γ ≤ ∑ d ∈ P.divisors.erase 1,
        (E * (|coefficient P d| / d.totient) +
          (1 / (normalizer P * Real.log Y)) * ((d : ℝ) ^ γ / d.totient)) :=
      Finset.sum_le_sum hpoint
    _ = E + (1 / (normalizer P * Real.log Y)) *
        ∑ d ∈ P.divisors.erase 1, (d : ℝ) ^ γ / d.totient := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsmall, mul_one]
    _ ≤ E + (1 / (normalizer P * Real.log Y)) * divisorEulerMoment P γ :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hlarge (one_div_nonneg.mpr hden.le))
    _ = E + divisorEulerMoment P γ / (normalizer P * Real.log Y) := by ring
end LongGapsBetweenPrimes
