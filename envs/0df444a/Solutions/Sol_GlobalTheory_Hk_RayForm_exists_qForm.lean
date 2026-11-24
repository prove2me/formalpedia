-- Prove2me | solution 1 for GlobalTheory.Hk.RayForm.exists_qForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:32:26.019883+00:00
-- url     : https://prove2.me/submissions/67b01a7d-e3c3-4271-9112-39dd2291fc56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_PlaneLatticeShortBasisOfBoundPowTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayClassPartialZetaContinuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_RingOfIntegersSqrtNegThreeModFour
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassIdealCountEqNcardShiftedBinaryForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.RayForm
open GlobalTheory.Mem.PartialZeta
namespace GlobalTheory.Hk.RayForm
theorem _root_.solution (f₁ f₂ x₀ : ℂ) (N : ℝ) (hN : N ≠ 0) (hA : ((starRingEnd ℂ) f₁ * f₂).im ≠ 0) :
    ∃ l θ₁ θ₂ : ℝ, ∀ v : ℤ × ℤ,
      qForm (‖f₁‖ ^ 2 / N) (((starRingEnd ℂ) f₁ * f₂).im ^ 2 / (‖f₁‖ ^ 2 * N)) l θ₁ θ₂ v =
        ‖x₀ + (v.1 * f₁ + v.2 * f₂)‖ ^ 2 / N := by
  have hf : f₁ ≠ 0 := by
    rintro rfl
    simp at hA
  have e1 : ((starRingEnd ℂ) f₁ * f₂).re = f₁.re * f₂.re + f₁.im * f₂.im := by
    simp [Complex.mul_re]
  have e2 : ((starRingEnd ℂ) f₁ * f₂).im = f₁.re * f₂.im - f₁.im * f₂.re := by
    simp [Complex.mul_im]
    ring
  have e3 : ((starRingEnd ℂ) f₁ * x₀).re = f₁.re * x₀.re + f₁.im * x₀.im := by
    simp [Complex.mul_re]
  have e4 : ((starRingEnd ℂ) f₁ * x₀).im = f₁.re * x₀.im - f₁.im * x₀.re := by
    simp [Complex.mul_im]
    ring
  have e5 : ‖f₁‖ ^ 2 = f₁.re ^ 2 + f₁.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hS : f₁.re ^ 2 + f₁.im ^ 2 ≠ 0 := by
    rw [← e5]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hf)
  refine ⟨((starRingEnd ℂ) f₁ * f₂).re / ‖f₁‖ ^ 2, ((starRingEnd ℂ) f₁ * x₀).re / ‖f₁‖ ^ 2,
    ((starRingEnd ℂ) f₁ * x₀).im / ((starRingEnd ℂ) f₁ * f₂).im, fun v => ?_⟩
  have e6 : ‖x₀ + ((v.1 : ℂ) * f₁ + (v.2 : ℂ) * f₂)‖ ^ 2 =
      (x₀.re + v.1 * f₁.re + v.2 * f₂.re) ^ 2 + (x₀.im + v.1 * f₁.im + v.2 * f₂.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  rw [e2] at hA
  simp only [qForm]
  rw [e6, e1, e2, e3, e4, e5]
  field_simp
  ring
end GlobalTheory.Hk.RayForm
