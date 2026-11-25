-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.abs_mul_norm_khat_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:11:47.90928+00:00
-- url     : https://prove2.me/submissions/47789114-4a5a-4b4d-b961-5c50b6503a2e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineKernel
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_step_identity
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_rem_nonneg
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_integral_rem_le
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
    |ξ| * ‖khat a r ξ‖ ≤ a / π := by
  set c : ℂ := ↑(-2 * π * ξ) * Complex.I with hc
  set F : ℝ → ℂ := fun t => Complex.exp (↑(-2 * π * t * ξ) * Complex.I) with hF
  have hFd : ∀ t, HasDerivAt F (F t * c) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => ((-2 * π * t * ξ : ℝ) : ℂ)) ((-2 * π * ξ : ℝ) : ℂ) t := by
      have := (((hasDerivAt_id t).const_mul (-2 * π)).mul_const ξ).ofReal_comp
      simpa using this
    exact (h1.mul_const Complex.I).cexp
  have hFc : Continuous F := by simp only [hF]; fun_prop
  have hstep := step_identity ha hr hFd (hFc.mul continuous_const)
  have hF0 : F 0 = 1 := by simp [hF]
  rw [hF0] at hstep
  have e1 : ∫ t, (F t - (a : ℂ)⁻¹ * (F t * c)) * (kern a r t : ℂ) =
      (1 - (a : ℂ)⁻¹ * c) * khat a r ξ := by
    rw [khat_eq, ← integral_const_mul]
    congr 1; funext t; simp only [hF]; ring
  rw [e1] at hstep
  have hrem : ‖∫ t, F t * (rem a r t : ℂ)‖ ≤ 1 := by
    refine (norm_integral_le_integral_norm _).trans ?_
    have : (fun t => ‖F t * (rem a r t : ℂ)‖) = fun t => rem a r t := by
      funext t
      rw [norm_mul, hF, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (rem_nonneg hr t)]
    rw [this]
    exact (integral_rem_le ha.le hr).trans (exp_le_one_iff.2 (by nlinarith))
  have hkey : (1 - (a : ℂ)⁻¹ * c) * khat a r ξ = 1 - ∫ t, F t * (rem a r t : ℂ) := by
    linear_combination (-1 : ℂ) * hstep
  have hn : ‖(1 - (a : ℂ)⁻¹ * c) * khat a r ξ‖ ≤ 2 := by
    rw [hkey]; exact (norm_sub_le _ _).trans (by simp; linarith)
  have him : |2 * π * ξ / a| ≤ ‖1 - (a : ℂ)⁻¹ * c‖ := by
    refine le_trans (le_of_eq ?_) (Complex.abs_im_le_norm _)
    simp only [hc, Complex.sub_im, Complex.one_im, Complex.mul_im, Complex.inv_re,
      Complex.inv_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.normSq_ofReal]
    congr 1
    field_simp
    ring
  rw [norm_mul] at hn
  have hpos : 0 < 2 * π / a := by positivity
  have h3 : |2 * π * ξ / a| = 2 * π / a * |ξ| := by
    rw [show 2 * π * ξ / a = 2 * π / a * ξ by ring, abs_mul, abs_of_pos hpos]
  rw [h3] at him
  have h4 : 2 * π / a * (|ξ| * ‖khat a r ξ‖) ≤ 2 := by
    calc 2 * π / a * (|ξ| * ‖khat a r ξ‖) = (2 * π / a * |ξ|) * ‖khat a r ξ‖ := by ring
      _ ≤ ‖1 - (a : ℂ)⁻¹ * c‖ * ‖khat a r ξ‖ := by gcongr
      _ ≤ 2 := hn
  have := mul_le_mul_of_nonneg_left h4 (le_of_lt (by positivity : (0 : ℝ) < a / (2 * π)))
  have e : a / (2 * π) * (2 * π / a * (|ξ| * ‖khat a r ξ‖)) = |ξ| * ‖khat a r ξ‖ := by
    field_simp
  rw [e] at this
  calc |ξ| * ‖khat a r ξ‖ ≤ a / (2 * π) * 2 := this
    _ = a / π := by field_simp
end GroundTheory.Automorphic.LineKernel
