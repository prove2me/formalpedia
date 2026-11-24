-- Prove2me | solution 1 for GlobalTheory.RealWeil.CoefQDecay.norm_integral_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:55:15.170919+00:00
-- url     : https://prove2.me/submissions/26f0fda6-67cd-4996-854d-82790c83a8a6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MatrixCoeffDecaySecondPart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap
open scoped FourierTransform ContDiff RealInnerProductSpace Real
noncomputable section
open GlobalTheory GlobalTheory.RealWeil GlobalTheory.RealWeil.CoefQDecay
variable {n : ℕ}
namespace GlobalTheory.RealWeil.CoefQDecay
theorem _root_.solution (g g' : Sch (Fin n)) (w : Fin n ⊕ Fin n → ℝ) :
    ‖∫ x, rhoFun w ⇑g x * starRingEnd ℂ (g' x)‖ = ‖𝓕 (prodTrans g g' (pPart w)) (-qPart w)‖ := by
  have e : (fun x => rhoFun w ⇑g x * starRingEnd ℂ (g' x)) = fun x =>
      Complex.exp (((π * ⟪pPart w, qPart w⟫ : ℝ) : ℂ) * Complex.I) *
        (𝐞 (-⟪x, -qPart w⟫) • prodTrans g g' (pPart w) x) := by
    funext x
    simp only [rhoFun, phase, prodTrans, Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
    have h : Complex.exp (((2 * π * ⟪qPart w, x⟫ + π * ⟪pPart w, qPart w⟫ : ℝ) : ℂ) * Complex.I) =
        Complex.exp (((π * ⟪pPart w, qPart w⟫ : ℝ) : ℂ) * Complex.I) *
          Complex.exp (((2 * π * -⟪x, -qPart w⟫ : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      rw [inner_neg_right, neg_neg, real_inner_comm]
      push_cast
      ring
    rw [h]
    ring
  rw [e, integral_const_mul, Real.fourier_eq, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
end GlobalTheory.RealWeil.CoefQDecay
