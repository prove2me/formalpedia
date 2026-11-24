-- Prove2me | solution 1 for GlobalTheory.Hk.RayForm.comb_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:32:24.256501+00:00
-- url     : https://prove2.me/submissions/714f50bb-316c-49ff-802b-86c7c698cb9d

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
theorem _root_.solution (f₁ f₂ : ℂ) (hA : ((starRingEnd ℂ) f₁ * f₂).im ≠ 0) :
    Function.Injective (fun v : ℤ × ℤ => (v.1 : ℂ) * f₁ + v.2 * f₂) := by
  have hf : f₁ ≠ 0 := by
    rintro rfl
    simp at hA
  have key : ∀ x y : ℤ, (x : ℂ) * f₁ + y * f₂ = 0 → x = 0 ∧ y = 0 := by
    intro x y h
    have him : ((starRingEnd ℂ) f₁ * ((x : ℂ) * f₁ + y * f₂)).im =
        y * ((starRingEnd ℂ) f₁ * f₂).im := by
      simp only [Complex.mul_im, Complex.mul_re, Complex.add_re, Complex.add_im,
        Complex.conj_re, Complex.conj_im, Complex.intCast_re, Complex.intCast_im]
      ring
    rw [h, mul_zero, Complex.zero_im] at him
    have hy : y = 0 := by
      have : (y : ℝ) = 0 := by
        rcases mul_eq_zero.mp him.symm with h' | h'
        · exact h'
        · exact absurd h' hA
      exact_mod_cast this
    subst hy
    refine ⟨?_, rfl⟩
    simp only [Int.cast_zero, zero_mul, add_zero, mul_eq_zero, hf, or_false] at h
    exact_mod_cast h
  intro v w hvw
  have := key (v.1 - w.1) (v.2 - w.2) (by push_cast; linear_combination hvw)
  exact Prod.ext (sub_eq_zero.mp this.1) (sub_eq_zero.mp this.2)
end GlobalTheory.Hk.RayForm
