-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.HDecay.wF_integrable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:21:07.089202+00:00
-- url     : https://prove2.me/submissions/6c323d4a-8e69-45cd-98f1-32c409adb516

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierTransformRapidDecay
import Theorems.Thm_GlobalTheory_HeckeTwo_HDecay_sq_add_sq_pos
import Theorems.Thm_GlobalTheory_HeckeTwo_HDecay_hasDerivAt_wF

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Complex MeasureTheory
open scoped ContDiff FourierTransform
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.HDecay
variable (σ : ℂ) (y : ℝ)
variable {σ y}
namespace GlobalTheory.HeckeTwo.HDecay
theorem _root_.solution (hy : y ≠ 0) (hσ : 0 < σ.re) (a b : ℕ) : Integrable (wF σ y a b) := by
  have hc : Continuous (wF σ y a b) :=
    continuous_iff_continuousAt.2 fun t => (hasDerivAt_wF σ hy a b t).continuousAt
  have hy2 : 0 < y ^ 2 := lt_of_le_of_ne (sq_nonneg y) (Ne.symm (pow_ne_zero 2 hy))
  have hay : 0 < |y| := abs_pos.2 hy
  set K := (1 + (y ^ 2)⁻¹) * |y|⁻¹ ^ (a + b) * Real.exp (-σ.re * Real.log (y ^ 2)) with hK
  refine (integrable_inv_one_add_sq.const_mul K).mono' hc.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => ?_)
  have hpos := sq_add_sq_pos hy t
  have hnorm : ‖(t : ℂ) + (y : ℂ) * I‖ ^ 2 = t ^ 2 + y ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_add_mul_I]
  have hnorm' : ‖(t : ℂ) - (y : ℂ) * I‖ ^ 2 = t ^ 2 + y ^ 2 := by
    rw [Complex.sq_norm, sub_eq_add_neg, ← neg_mul, ← Complex.ofReal_neg, Complex.normSq_add_mul_I]
    ring
  have him : |y| ≤ ‖(t : ℂ) + (y : ℂ) * I‖ := by
    have := Complex.abs_im_le_norm ((t : ℂ) + (y : ℂ) * I)
    simpa using this
  have him' : |y| ≤ ‖(t : ℂ) - (y : ℂ) * I‖ := by
    have := Complex.abs_im_le_norm ((t : ℂ) - (y : ℂ) * I)
    simpa using this
  have hg1 : ‖gI y t‖ ≤ |y|⁻¹ := by
    rw [gI, norm_inv]
    exact inv_anti₀ hay him
  have hh1 : ‖hI y t‖ ≤ |y|⁻¹ := by
    rw [hI, norm_inv]
    exact inv_anti₀ hay him'
  have hg2 : ‖gI y t‖ ^ 2 ≤ (1 + (y ^ 2)⁻¹) * (1 + t ^ 2)⁻¹ := by
    rw [gI, norm_inv, inv_pow, hnorm]
    have key : 1 + t ^ 2 ≤ (1 + (y ^ 2)⁻¹) * (t ^ 2 + y ^ 2) := by
      rw [add_mul, one_mul, inv_mul_eq_div, add_div, div_self hy2.ne']
      have : 0 ≤ t ^ 2 / y ^ 2 := by positivity
      nlinarith
    calc (t ^ 2 + y ^ 2)⁻¹ = (1 + (y ^ 2)⁻¹) * ((1 + (y ^ 2)⁻¹) * (t ^ 2 + y ^ 2))⁻¹ := by
          field_simp
      _ ≤ (1 + (y ^ 2)⁻¹) * (1 + t ^ 2)⁻¹ := by gcongr
  have hE : ‖eF σ y t‖ ≤ Real.exp (-σ.re * Real.log (y ^ 2)) := by
    rw [eF, Complex.norm_exp]
    apply Real.exp_le_exp.2
    have hre : (-σ * (Real.log (t ^ 2 + y ^ 2) : ℂ)).re = -σ.re * Real.log (t ^ 2 + y ^ 2) := by
      simp [Complex.mul_re]
    rw [hre]
    have hlog : Real.log (y ^ 2) ≤ Real.log (t ^ 2 + y ^ 2) :=
      Real.log_le_log hy2 (by nlinarith [sq_nonneg t])
    nlinarith
  calc ‖wF σ y a b t‖ = ‖gI y t‖ ^ 2 * ‖gI y t‖ ^ a * ‖hI y t‖ ^ b * ‖eF σ y t‖ := by
        simp only [wF, norm_mul, norm_pow]
        ring
    _ ≤ ((1 + (y ^ 2)⁻¹) * (1 + t ^ 2)⁻¹) * |y|⁻¹ ^ a * |y|⁻¹ ^ b *
          Real.exp (-σ.re * Real.log (y ^ 2)) := by gcongr
    _ = K * (1 + t ^ 2)⁻¹ := by
        rw [hK]
        ring
end GlobalTheory.HeckeTwo.HDecay
