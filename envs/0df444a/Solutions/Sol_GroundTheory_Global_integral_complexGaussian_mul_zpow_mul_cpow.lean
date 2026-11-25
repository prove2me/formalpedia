-- Prove2me | solution 1 for GroundTheory.Global.integral_complexGaussian_mul_zpow_mul_cpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:09:59.776448+00:00
-- url     : https://prove2.me/submissions/d826a561-092c-41c6-b363-c5393f34909e

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_Gaussian
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianComplex
import Theorems.Thm_P2M_GroundTheory_Global_traceForm__apply_f7b017a4f6bf
import Theorems.Thm_GroundTheory_Global_complexGaussian_mul_zpow
import Theorems.Thm_GroundTheory_Global_integral_comp_norm_complexPlaceMeasure
import Theorems.Thm_GroundTheory_Global_mellin_exp_neg_mul_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.traceFormℂ_apply

set_option autoImplicit false
open GroundTheory GroundTheory.Global
open Complex MeasureTheory Set Real ComplexConjugate
open scoped FourierTransform ENNReal
noncomputable section
namespace GroundTheory.Global
theorem _root_.solution (m : ℤ) {s : ℂ}
    (hs : 0 < s.re + m.natAbs / 2) :
    ∫ z, complexGaussian m z * (z / (‖z‖ : ℂ)) ^ (-m) * ((‖z‖ ^ 2 : ℝ) : ℂ) ^ s /
        ((‖z‖ ^ 2 : ℝ) : ℂ) ∂complexPlaceMeasure =
      π * Gammaℂ (s + m.natAbs / 2) := by
  set n := m.natAbs with hn
  have h : (fun z : ℂ ↦ complexGaussian m z * (z / (‖z‖ : ℂ)) ^ (-m) *
        ((‖z‖ ^ 2 : ℝ) : ℂ) ^ s / ((‖z‖ ^ 2 : ℝ) : ℂ)) =
      fun z ↦ (fun y : ℝ ↦ (y : ℂ) ^ n * ((Real.exp (-(2 * π * y ^ 2)) : ℝ) : ℂ) *
        ((y ^ 2 : ℝ) : ℂ) ^ s / ((y ^ 2 : ℝ) : ℂ)) ‖z‖ := by
    funext z
    by_cases hz : z = 0
    · subst hz; simp
    · simp only
      rw [complexGaussian_mul_zpow hz, ofReal_exp, ← hn]
      push_cast
      ring_nf
  rw [h, integral_comp_norm_complexPlaceMeasure (fun y : ℝ ↦ (y : ℂ) ^ n *
    ((Real.exp (-(2 * π * y ^ 2)) : ℝ) : ℂ) * ((y ^ 2 : ℝ) : ℂ) ^ s / ((y ^ 2 : ℝ) : ℂ))]
  have ha : 0 < (2 * s + n).re := by simp; linarith
  have : ∫ y in Ioi (0 : ℝ), (y : ℂ) * ((y : ℂ) ^ n * ((Real.exp (-(2 * π * y ^ 2)) : ℝ) : ℂ) *
        ((y ^ 2 : ℝ) : ℂ) ^ s / ((y ^ 2 : ℝ) : ℂ)) =
      mellin (fun t : ℝ ↦ ((Real.exp (-(2 * π * t ^ 2)) : ℝ) : ℂ)) (2 * s + n) := by
    rw [mellin]
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy ↦ ?_
    have hy0 : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hy)
    have e1 : ((y ^ 2 : ℝ) : ℂ) ^ s = (y : ℂ) ^ (((2 : ℝ) : ℂ) * s) := by
      rw [cpow_mul_ofReal_nonneg (le_of_lt hy), Real.rpow_two]
    have e2 : (y : ℂ) ^ (2 * s + n - 1) = (y : ℂ) ^ (((2 : ℝ) : ℂ) * s) * (y : ℂ) ^ n / y := by
      rw [cpow_sub _ _ hy0, cpow_add _ _ hy0, cpow_natCast, cpow_one]; push_cast; ring
    rw [e1, e2, smul_eq_mul]
    push_cast
    field_simp
  rw [this, mellin_exp_neg_mul_sq (by positivity) ha, Gammaℂ_def]
  have e3 : (2 * s + n) / 2 = s + n / 2 := by ring
  rw [e3]
  push_cast
  ring
end GroundTheory.Global
