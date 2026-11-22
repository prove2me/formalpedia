-- Prove2me | solution 1 for LongGapsBetweenPrimes.sieve_normalizer_lower_of_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:05:07.382542+00:00
-- url     : https://prove2.me/submissions/7ad7d508-f975-47d3-bbf7-d0f429edd78e

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_eulerProduct_one_le
import Theorems.Thm_LongGapsBetweenPrimes_normalizer_lower_bound

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {x : ℝ} (hx : 0 < x)
    (hlx : 1 ≤ Real.log x) (hZ : 2 ≤ sieveZ x)
    (hlarge : 7 * Real.exp 6 * (Real.log x) ^ 6 ≤ x)
    (hsmall : 6 * Real.log (Real.log x) + Real.log 7 + 8 ≤ Real.log x / 2) :
    sieveZ x ≤ sieveY x ∧ normalizerLower ≤ normalizer (sieveP x) := by
  have hlxpos : 0 < Real.log x := zero_lt_one.trans_le hlx
  have hexp : 1 ≤ Real.exp 6 := Real.one_le_exp (by norm_num)
  have hscale : 7 * Real.exp 6 * Real.log x ≤ sieveUpperLog x := by
    apply (le_div_iff₀ (pow_pos hlxpos 5)).mpr
    nlinarith [hlarge]
  have hZY : sieveZ x ≤ sieveY x := by
    apply Nat.floor_le_floor
    calc
      x ^ 6 = Real.exp (6 * Real.log x) := by
        simpa only [Nat.cast_ofNat, Real.exp_log hx] using
          (Real.exp_nat_mul (Real.log x) 6).symm
      _ ≤ Real.exp (sieveUpperLog x) := Real.exp_le_exp.mpr (by
        nlinarith [mul_le_mul_of_nonneg_right hexp hlxpos.le])
  refine ⟨hZY, ?_⟩
  have hlogZ : Real.log (sieveZ x) ≤ 6 * Real.log x := by
    calc
      _ ≤ Real.log (x ^ 6) := Real.log_le_log
        (by exact_mod_cast (by omega : 0 < sieveZ x)) (Nat.floor_le (by positivity))
      _ = _ := by rw [Real.log_pow]; norm_num
  have hZA : eulerProduct (sieveZ x) 1 ≤ 7 * Real.exp 6 * Real.log x := by
    calc
      _ ≤ Real.exp 6 * (1 + Real.log (sieveZ x)) := eulerProduct_one_le hZ
      _ ≤ Real.exp 6 * (7 * Real.log x) :=
        mul_le_mul_of_nonneg_left (by linarith) (Real.exp_nonneg 6)
      _ = _ := by ring
  have hYlog : sieveUpperLog x ≤ Real.log ((sieveY x : ℝ) + 1) := by
    calc
      _ = Real.log (Real.exp (sieveUpperLog x)) := (Real.log_exp _).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos _) (Nat.lt_floor_add_one _).le
  have hApos : 0 < 7 * Real.exp 6 * Real.log x := by positivity
  have hbound := normalizer_lower_bound hZY hApos hZA (hscale.trans hYlog)
  have hloglog : Real.log x - 5 * Real.log (Real.log x) ≤
      Real.log (Real.log ((sieveY x : ℝ) + 1)) := by
    calc
      _ = Real.log (sieveUpperLog x) := by
        rw [sieveUpperLog, Real.log_div hx.ne' (pow_pos hlxpos 5).ne', Real.log_pow]
        norm_num
      _ ≤ _ := Real.log_le_log (hApos.trans_le hscale) hYlog
  have hlogA : Real.log (7 * Real.exp 6 * Real.log x) =
      Real.log 7 + 6 + Real.log (Real.log x) := by
    rw [Real.log_mul (by positivity : (7 * Real.exp 6 : ℝ) ≠ 0) hlxpos.ne',
      Real.log_mul (by norm_num : (7 : ℝ) ≠ 0) (Real.exp_ne_zero 6), Real.log_exp]
  rw [hlogA] at hbound
  have hlower : Real.log x / 2 ≤
      2 * (7 * Real.exp 6 * Real.log x) * normalizer (sieveP x) := by
    change _ ≤ 2 * (7 * Real.exp 6 * Real.log x) *
      normalizer (auxiliaryProduct (sieveZ x) (sieveY x))
    linarith
  unfold normalizerLower
  apply (div_le_iff₀ (by positivity : 0 < 100 * Real.exp 6)).mpr
  nlinarith
end LongGapsBetweenPrimes
