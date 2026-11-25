-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.norm_khat_sub_one_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:18:15.346684+00:00
-- url     : https://prove2.me/submissions/b26672e6-9e09-460d-9c4f-213298b7e9d1

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineKernel
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_kern_nonneg
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_support_kern_subset
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_integrable_kern
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_integral_kern_le_one
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_one_sub_exp_le_integral_kern
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_khat_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Set Filter Topology Real Function
open scoped ContDiff FourierTransform
noncomputable section
open GroundTheory.Automorphic.LineKernel
namespace GroundTheory.Automorphic.LineKernel
theorem _root_.solution {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (ξ : ℝ) :
    ‖khat a r ξ - 1‖ ≤ 4 * π * r * |ξ| + exp (-a * r) := by
  have hk := integrable_kern ha.le hr
  have hkc : Integrable fun t => (kern a r t : ℂ) := hk.ofReal
  set F : ℝ → ℂ := fun t => Complex.exp (↑(-2 * π * t * ξ) * Complex.I) with hF
  have hFc : Continuous F := by simp only [hF]; fun_prop
  have hint1 : Integrable fun t => F t * (kern a r t : ℂ) := by
    refine hkc.bdd_mul (c := 1) hFc.aestronglyMeasurable ?_
    filter_upwards with t
    rw [show F t = Complex.exp (↑(-2 * π * t * ξ) * Complex.I) from rfl,
      Complex.norm_exp_ofReal_mul_I]
  have hsplit : khat a r ξ - 1 = (∫ t, (F t - 1) * (kern a r t : ℂ)) +
      (((∫ t, kern a r t) - 1 : ℝ) : ℂ) := by
    have hkF : khat a r ξ = ∫ t, F t * (kern a r t : ℂ) := khat_eq a r ξ
    have h2 : ∫ t, (F t - 1) * (kern a r t : ℂ) =
        (∫ t, F t * (kern a r t : ℂ)) - ∫ t, (kern a r t : ℂ) := by
      simp only [sub_mul, one_mul]; exact integral_sub hint1 hkc
    rw [hkF, h2, integral_complex_ofReal]
    push_cast; ring
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (norm_integral_le_integral_norm _).trans ?_
    calc ∫ t, ‖(F t - 1) * (kern a r t : ℂ)‖ ≤ ∫ t, 4 * π * r * |ξ| * kern a r t := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun t => norm_nonneg _)
            (hk.const_mul _) (Eventually.of_forall fun t => ?_)
          dsimp only
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (kern_nonneg ha.le r t)]
          by_cases ht : t ∈ Icc 0 (2 * r)
          · have h1 : ‖F t - 1‖ ≤ |-2 * π * t * ξ| := by
              have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := -2 * π * t * ξ)
              simpa [hF, mul_comm] using this
            have h2 : |-2 * π * t * ξ| ≤ 4 * π * r * |ξ| := by
              rw [show -2 * π * t * ξ = -(2 * π * t) * ξ by ring, abs_mul, abs_neg,
                abs_of_nonneg (by nlinarith [ht.1, pi_pos] : (0:ℝ) ≤ 2 * π * t)]
              have := ht.2
              have : 2 * π * t ≤ 4 * π * r := by nlinarith [pi_pos]
              exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
            exact mul_le_mul_of_nonneg_right (h1.trans h2) (kern_nonneg ha.le r t)
          · have : kern a r t = 0 := by
              by_contra h; exact ht (support_kern_subset hr h)
            simp [this]
      _ ≤ 4 * π * r * |ξ| := by
          rw [integral_const_mul]
          have := integral_kern_le_one ha hr
          have : 0 ≤ 4 * π * r * |ξ| := by positivity
          nlinarith
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg (by linarith [integral_kern_le_one ha hr])]
    linarith [one_sub_exp_le_integral_kern ha hr]
end GroundTheory.Automorphic.LineKernel
