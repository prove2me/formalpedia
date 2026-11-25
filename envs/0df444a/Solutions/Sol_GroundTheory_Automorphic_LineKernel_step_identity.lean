-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.step_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:59:34.079985+00:00
-- url     : https://prove2.me/submissions/839471c9-2634-462f-a5dd-518ad69e0818

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineKernel
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_contDiff_cutoff
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_cutoff_eq_one
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_cutoff_eq_zero
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_kern_eq_zero_of_neg
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_kern_eq_zero_of_ge
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_kern_of_nonneg
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_contDiff_deriv_cutoff
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_contDiff_rem
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_rem_eq_zero
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_integral_eq_intervalIntegral

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
theorem _root_.solution {a r : ℝ} (ha : 0 < a) (hr : 0 < r) {F F' : ℝ → ℂ}
    (hF : ∀ t, HasDerivAt F (F' t) t) (hF' : Continuous F') :
    F 0 = (∫ t, (F t - (a : ℂ)⁻¹ * F' t) * (kern a r t : ℂ)) + ∫ t, F t * (rem a r t : ℂ) := by
  have hb : (0 : ℝ) ≤ 2 * r := by linarith
  have e1 : ∫ t, (F t - (a : ℂ)⁻¹ * F' t) * (kern a r t : ℂ) =
      ∫ t in (0 : ℝ)..2 * r, (F t - (a : ℂ)⁻¹ * F' t) * (kern a r t : ℂ) := by
    refine integral_eq_intervalIntegral hb fun t ht => ?_
    rcases not_and_or.1 ht with h | h
    · rw [kern_eq_zero_of_neg (not_le.1 h)]; simp
    · rw [kern_eq_zero_of_ge hr (not_le.1 h).le]; simp
  have e2 : ∫ t, F t * (rem a r t : ℂ) = ∫ t in (0 : ℝ)..2 * r, F t * (rem a r t : ℂ) := by
    refine integral_eq_intervalIntegral hb fun t ht => ?_
    rw [rem_eq_zero hr (fun h => ht ⟨hr.le.trans h.1, h.2⟩)]; simp
  suffices hsuff : F 0 = (∫ t in (0 : ℝ)..2 * r, (F t - (a : ℂ)⁻¹ * F' t) * (kern a r t : ℂ)) +
      ∫ t in (0 : ℝ)..2 * r, F t * (rem a r t : ℂ) by
    rw [hsuff, ← e1, ← e2]
  have hFc : Continuous F := continuous_iff_continuousAt.2 fun t => (hF t).continuousAt
  set E : ℝ → ℝ := fun t => exp (-a * t) with hE
  set χ := cutoff r with hχ
  set χ' := deriv (cutoff r) with hχ'
  have hEd : ∀ t, HasDerivAt E (-a * E t) t := by
    intro t
    have := ((hasDerivAt_id t).const_mul (-a)).exp
    simpa [hE, mul_comm] using this
  have hχd : ∀ t, HasDerivAt χ (χ' t) t := fun t =>
    ((contDiff_cutoff r (n := 1)).differentiable one_ne_zero t).hasDerivAt
  have hEc : Continuous E := continuous_exp.comp (continuous_const.mul continuous_id)
  have hχc : Continuous χ := (contDiff_cutoff r (n := 0)).continuous
  have hχ'c : Continuous χ' := (contDiff_deriv_cutoff r).continuous
  set φ : ℝ → ℂ := fun t => F t * ((E t * χ t : ℝ) : ℂ) with hφ
  set φ' : ℝ → ℂ := fun t => F' t * ((E t * χ t : ℝ) : ℂ) +
    F t * ((-a * E t * χ t + E t * χ' t : ℝ) : ℂ) with hφ'
  have hφd : ∀ t, HasDerivAt φ (φ' t) t := by
    intro t
    have h1 : HasDerivAt (fun t => E t * χ t) (-a * E t * χ t + E t * χ' t) t := by
      exact (hEd t).mul (hχd t)
    exact (hF t).mul h1.ofReal_comp
  have hφ'c : Continuous φ' := by
    simp only [hφ']; fun_prop
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 2 * r)
    (fun t _ => hφd t) (hφ'c.intervalIntegrable _ _)
  have hc0 : cutoff r 0 = 1 := cutoff_eq_one hr hr.le
  have hφ0 : φ 0 = F 0 := by simp [hφ, hE, hχ, hc0]
  have hφ2 : φ (2 * r) = 0 := by simp [hφ, hχ, cutoff_eq_zero hr le_rfl]
  rw [hφ0, hφ2, zero_sub] at hFTC
  · rw [← intervalIntegral.integral_add]
    · have : ∫ t in (0 : ℝ)..2 * r, ((F t - (a : ℂ)⁻¹ * F' t) * (kern a r t : ℂ) +
          F t * (rem a r t : ℂ)) = ∫ t in (0 : ℝ)..2 * r, -φ' t := by
        refine intervalIntegral.integral_congr fun t ht => ?_
        rw [uIcc_of_le hb] at ht
        simp only [hφ', kern_of_nonneg ht.1, rem, hE, hχ, hχ']
        have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
        push_cast
        field_simp
        ring
      rw [this, intervalIntegral.integral_neg, hFTC, neg_neg]
    · refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hb]
      have : EqOn (fun t => (F t - (a : ℂ)⁻¹ * F' t) * (kern a r t : ℂ))
          (fun t => (F t - (a : ℂ)⁻¹ * F' t) * ((a * E t * χ t : ℝ) : ℂ)) (Icc 0 (2 * r)) := by
        intro t ht; simp only [kern_of_nonneg ht.1, hE, hχ]
      refine ContinuousOn.congr ?_ this
      exact Continuous.continuousOn (by fun_prop)
    · exact (Continuous.intervalIntegrable (by
        have : Continuous (rem a r) := (contDiff_rem a r).continuous
        fun_prop) _ _)
end GroundTheory.Automorphic.LineKernel
