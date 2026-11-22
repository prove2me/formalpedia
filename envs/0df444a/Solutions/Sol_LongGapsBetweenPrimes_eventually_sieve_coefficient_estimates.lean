-- Prove2me | solution 1 for LongGapsBetweenPrimes.eventually_sieve_coefficient_estimates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:08:26.044716+00:00
-- url     : https://prove2.me/submissions/78853e3c-8bdd-485b-88f6-5e15a6380265

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_normalizer_pos
import Theorems.Thm_LongGapsBetweenPrimes_auxiliaryProduct_squarefree
import Theorems.Thm_LongGapsBetweenPrimes_auxiliaryProduct_pos
import Theorems.Thm_LongGapsBetweenPrimes_auxiliary_coefficient_le_one
import Theorems.Thm_LongGapsBetweenPrimes_absoluteMomentBound_pos
import Theorems.Thm_LongGapsBetweenPrimes_coefficientControl_pos
import Theorems.Thm_LongGapsBetweenPrimes_auxiliary_coefficientAbsMoment_le
import Theorems.Thm_LongGapsBetweenPrimes_auxiliary_coefficientAbsMoment_control
import Theorems.Thm_LongGapsBetweenPrimes_normalizerLower_pos
import Theorems.Thm_LongGapsBetweenPrimes_tendsto_sieveZ
import Theorems.Thm_LongGapsBetweenPrimes_tendsto_log_sieveZ
import Theorems.Thm_LongGapsBetweenPrimes_eventually_sieve_normalizer_lower

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution : ∀ᶠ x : ℝ in Filter.atTop,
    0 < sieveBeta x ∧ CoefficientEstimates (sieveP x) (sieveBeta x) weightConstant := by
  have hunit := (Filter.Tendsto.const_mul_atTop normalizerLower_pos tendsto_log_sieveZ).eventually
    (Filter.eventually_ge_atTop (1 : ℝ))
  filter_upwards [eventually_sieve_normalizer_lower,
    tendsto_sieveZ.eventually (Filter.eventually_ge_atTop 2),
    tendsto_log_sieveZ.eventually (Filter.eventually_ge_atTop (1 : ℝ)),
    Filter.eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (1 : ℝ)), hunit]
    with x hB hZ hlogZ hx hlx hunit'
  obtain ⟨hZY, hB⟩ := hB
  have hx0 : 0 < x := by linarith
  have hlx0 : 0 < Real.log x := by linarith
  have hupper : 0 < sieveUpperLog x := div_pos hx0 (pow_pos hlx0 5)
  have hP : 1 < sieveP x := by
    have hp0 : 0 < sieveP x := auxiliaryProduct_pos _ _
    by_contra h
    have he : sieveP x = 1 := by omega
    have hb0 : normalizer (sieveP x) = 0 := by simp [he, normalizer]
    rw [hb0] at hB
    exact (not_le_of_gt normalizerLower_pos) hB
  have hY : 2 ≤ sieveY x := hZ.trans hZY
  have hY0 : (0 : ℝ) < sieveY x := by exact_mod_cast (by omega : 0 < sieveY x)
  have hYlog : Real.log (sieveY x : ℝ) ≤ sieveUpperLog x := by
    have h := Real.log_le_log hY0 (Nat.floor_le (Real.exp_pos (sieveUpperLog x)).le)
    simpa only [Real.log_exp] using h
  have hscale (γ : ℝ) (hγ : 0 ≤ γ) (hγβ : γ ≤ 2 * sieveBeta x) :
      γ * Real.log (sieveY x : ℝ) ≤ 2 := by
    calc
      _ ≤ γ * sieveUpperLog x := mul_le_mul_of_nonneg_left hYlog hγ
      _ ≤ (2 * sieveBeta x) * sieveUpperLog x := mul_le_mul_of_nonneg_right hγβ hupper.le
      _ = 2 := by unfold sieveBeta; field_simp
  have hC1 : absoluteMomentBound normalizerLower ≤ weightConstant := by
    unfold weightConstant
    have h := coefficientControl_pos normalizerLower_pos
    linarith
  have hC2 : coefficientControl normalizerLower ≤ weightConstant := by
    unfold weightConstant
    have h := absoluteMomentBound_pos normalizerLower_pos
    linarith
  refine ⟨one_div_pos.mpr hupper, ⟨hP, auxiliaryProduct_squarefree _ _, ?_, ?_, ?_⟩⟩
  · intro d hd
    exact auxiliary_coefficient_le_one hP (by omega : 1 < sieveZ x)
      (hunit'.trans (mul_le_mul_of_nonneg_right hB (by linarith : 0 ≤ Real.log (sieveZ x : ℝ)))) hd
  · intro γ hγ hγβ
    exact (auxiliary_coefficientAbsMoment_le hZY hZ hlogZ hP normalizerLower_pos hB hγ
      (hscale γ hγ hγβ)).trans hC1
  · intro γ hγ hγβ
    exact (auxiliary_coefficientAbsMoment_control hZY hZ hlogZ hP normalizerLower_pos hB hγ
      (hscale γ hγ hγβ)).trans (mul_le_mul_of_nonneg_right hC2 (normalizer_pos hP).le)
end LongGapsBetweenPrimes
