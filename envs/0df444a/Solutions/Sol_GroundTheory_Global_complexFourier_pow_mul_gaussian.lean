-- Prove2me | solution 1 for GroundTheory.Global.complexFourier_pow_mul_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:44:53.636004+00:00
-- url     : https://prove2.me/submissions/837f95bb-fa4d-43a4-be21-258ef0d830ae

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianComplex
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianComplexFourier
import Theorems.Thm_GroundTheory_Global_complexFourier_mul_self
import Theorems.Thm_GroundTheory_Global_exists_hasFDerivAt_conj_pow_mul_gaussian
import Theorems.Thm_GroundTheory_Global_complexGaussian_natCast
import Theorems.Thm_GroundTheory_Global_complexFourier_complexGaussian_zero
import Theorems.Thm_GroundTheory_Global_complexGaussian_zero
import Theorems.Thm_GroundTheory_Global_integrable_complexGaussian
import Theorems.Thm_P2M_GroundTheory_Global_integrable_norm_pow_smul_complexGaussian__d495b7190450
import Theorems.Thm_P2M_GroundTheory_Global_traceForm__apply_f7b017a4f6bf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Global_traceForm__apply_f7b017a4f6bf



set_option autoImplicit false
open GroundTheory GroundTheory.Global
open Complex MeasureTheory Set Real ComplexConjugate
open scoped FourierTransform
noncomputable section
namespace GroundTheory.Global
theorem _root_.solution (n : ℕ) :
    complexFourier (fun z ↦ z ^ n * Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2)) =
      fun w ↦ (-I) ^ n * (conj w ^ n * Complex.exp (-2 * π * (‖w‖ : ℂ) ^ 2)) := by
  induction n with
  | zero =>
    have h := complexFourier_complexGaussian_zero
    simp only [funext complexGaussian_zero] at h
    simpa using h
  | succ n ih =>
    funext w
    obtain ⟨D, hD, hD1⟩ := exists_hasFDerivAt_conj_pow_mul_gaussian n w
    have hF : HasFDerivAt (complexFourier (fun z ↦ z ^ n * Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2)))
        ((-I) ^ n • D) w := by
      rw [ih]; exact hD.const_mul _
    have hf : Integrable (fun z ↦ z ^ n * Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2))
        complexPlaceMeasure := by
      simpa [complexGaussian_natCast] using integrable_complexGaussian n
    have hf' : Integrable (fun z ↦ ‖z‖ * ‖z ^ n * Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2)‖)
        complexPlaceMeasure := by
      have := (integrable_norm_pow_smul_complexGaussian' n 1).norm
      refine this.congr (Filter.Eventually.of_forall fun z ↦ ?_)
      simp [complexGaussian_natCast]
    have key := complexFourier_mul_self hf hf' hF
    have e : (fun z : ℂ ↦ z * (z ^ n * Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2))) =
        fun z ↦ z ^ (n + 1) * Complex.exp (-2 * π * (‖z‖ : ℂ) ^ 2) := by
      funext z; ring
    rw [e] at key
    have hne : (-4 * π * I : ℂ) ≠ 0 := by
      have : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
      simp [this, I_ne_zero]
    apply mul_left_cancel₀ hne
    rw [key]
    simp only [smul_apply, smul_eq_mul]
    have hD1' : (-I) ^ n * D 1 - I * ((-I) ^ n * D I) = (-I) ^ n * (D 1 - I * D I) := by ring
    rw [hD1', hD1]
    rw [pow_succ]
    linear_combination (-4 * π * (-I) ^ n * (conj w ^ (n + 1) *
      Complex.exp (-2 * π * (‖w‖ : ℂ) ^ 2))) * I_sq
end GroundTheory.Global
