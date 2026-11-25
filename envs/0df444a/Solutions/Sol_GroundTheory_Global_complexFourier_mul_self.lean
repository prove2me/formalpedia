-- Prove2me | solution 1 for GroundTheory.Global.complexFourier_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:14:18.727997+00:00
-- url     : https://prove2.me/submissions/0161d374-d458-4f0f-92f4-bdc5b97d29fd

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianComplex
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianComplexFourier
import Theorems.Thm_GroundTheory_Global_complexFourier_eq_fourierIntegral
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
theorem _root_.solution {f : ℂ → ℂ} (hf : Integrable f complexPlaceMeasure)
    (hf' : Integrable (fun z ↦ ‖z‖ * ‖f z‖) complexPlaceMeasure) {w : ℂ} {D : ℂ →L[ℝ] ℂ}
    (hD : HasFDerivAt (complexFourier f) D w) :
    -4 * π * I * complexFourier (fun z ↦ z * f z) w = D 1 - I * D I := by
  have h := VectorFourier.hasFDerivAt_fourierIntegral traceFormℂ hf hf' w
  rw [← complexFourier_eq_fourierIntegral] at h
  rw [hD.unique h]
  have hint : Integrable (fun z ↦ VectorFourier.fourierSMulRight traceFormℂ f z)
      complexPlaceMeasure := by
    refine ((hf'.const_mul (2 * π * ‖traceFormℂ‖))).mono' hf.1.fourierSMulRight ?_
    refine Filter.Eventually.of_forall fun z ↦ ?_
    have := VectorFourier.norm_fourierSMulRight_le traceFormℂ f z
    simpa [mul_assoc] using this
  rw [fourierIntegral_continuousLinearMap_apply' hint,
    fourierIntegral_continuousLinearMap_apply' hint]
  have hL : ∀ v : ℂ, traceFormℂ.toLinearMap₁₂ v w = 2 * (v * w).re :=
    fun v ↦ traceFormℂ_apply v w
  simp only [VectorFourier.fourierIntegral, VectorFourier.fourierSMulRight_apply, hL,
    traceFormℂ_apply]
  have i1 : ∀ h : ℂ, Integrable (fun z ↦ 𝐞 (-(2 * (z * w).re)) •
      (-(2 * π * I) • (2 * (z * h).re) • f z)) complexPlaceMeasure := by
    intro h
    have : Integrable (fun z ↦ (-(2 * π * I) • (2 * (z * h).re) • f z)) complexPlaceMeasure := by
      have := (hint.apply_continuousLinearMap h)
      simpa [VectorFourier.fourierSMulRight_apply] using this
    have := (fourierIntegral_convergent_iff' (μ := complexPlaceMeasure) traceFormℂ w).2 this
    simpa using this
  rw [← integral_const_mul, ← integral_sub (i1 1) ((i1 I).const_mul I), complexFourier,
    ← integral_const_mul]
  congr 1
  funext z
  simp only [Circle.smul_def, smul_eq_mul, Complex.real_smul, mul_one, mul_I_re]
  push_cast
  have hz : (z : ℂ) = z.re + z.im * I := (re_add_im z).symm
  linear_combination (-4 * π * I * (𝐞 (-(2 * (z * w).re)) : ℂ) * f z) * hz
end GroundTheory.Global
