-- Prove2me | solution 1 for GlobalTheory.DerivativeOfAdditiveContinuous.hasDerivAt_of_continuous_of_map_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:19:11.955512+00:00
-- url     : https://prove2.me/submissions/c7852488-0d34-40fd-b69e-71a3bd3213e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasDerivAtOfContinuousOfMapAdd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DerivativeOfAdditiveContinuous
namespace GlobalTheory.DerivativeOfAdditiveContinuous
theorem _root_.solution (χ : ℝ → ℂ) (hc : Continuous χ)
    (hadd : ∀ s t : ℝ, χ (s + t) = χ s * χ t) (h0 : χ (0 : ℝ) = (1 : ℂ)) (s : ℝ) :
    HasDerivAt χ (deriv χ (0 : ℝ) * χ s) s := by
  obtain ⟨δ, hδ, hball⟩ := Metric.continuous_iff.mp hc 0 (1 / 2) (by norm_num)
  set η := δ / 2 with hη
  have hη0 : 0 < η := by positivity
  set c := ∫ t in (0 : ℝ)..η, χ t with hcdef
  have hc0 : c ≠ 0 := by
    have hsplit : c = (η : ℂ) + ∫ t in (0 : ℝ)..η, (χ t - 1) := by
      rw [hcdef, intervalIntegral.integral_sub (hc.intervalIntegrable _ _) intervalIntegrable_const]
      simp
    have hbound : ‖∫ t in (0 : ℝ)..η, (χ t - 1)‖ ≤ 1 / 2 * |η - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t ht
      rw [Set.uIoc_of_le hη0.le] at ht
      have h1 : dist t 0 < δ := by
        rw [Real.dist_eq, sub_zero, abs_of_pos ht.1]
        linarith [ht.2]
      have h2 := hball t h1
      rw [dist_eq_norm, h0] at h2
      exact h2.le
    intro hzero
    rw [hsplit] at hzero
    have h3 : ‖∫ t in (0 : ℝ)..η, (χ t - 1)‖ = η := by
      rw [eq_neg_of_add_eq_zero_right hzero, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hη0]
    rw [h3, sub_zero, abs_of_pos hη0] at hbound
    linarith
  set F : ℝ → ℂ := fun x => ∫ t in (0 : ℝ)..x, χ t with hF
  have hFd : ∀ x, HasDerivAt F (χ x) x := fun x => (hc.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hrep : ∀ x, χ x * c = F (x + η) - F x := by
    intro x
    have h1 : ∫ t in (0 : ℝ)..η, χ (x + t) = χ x * c := by
      simp only [hadd]
      rw [intervalIntegral.integral_const_mul]
    have h2 : ∫ t in (0 : ℝ)..η, χ (x + t) = ∫ t in x..(x + η), χ t := by
      rw [intervalIntegral.integral_comp_add_left]
      simp
    rw [← h1, h2, hF]
    simp only
    rw [intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)]
  have hdiff : ∀ x, DifferentiableAt ℝ χ x := by
    intro x
    have hχ : χ = fun y => (F (y + η) - F y) / c := by
      funext y
      rw [← hrep y, mul_div_cancel_right₀ _ hc0]
    rw [hχ]
    exact (((hFd (x + η)).comp_add_const x η).sub (hFd x)).differentiableAt.div_const c
  have hd0 : HasDerivAt χ (deriv χ 0) (s - s) := by
    rw [sub_self]
    exact (hdiff 0).hasDerivAt
  have hcomp : HasDerivAt (fun y => χ (y - s)) (deriv χ 0) s := hd0.comp_sub_const s s
  have hmul := hcomp.const_mul (χ s)
  have hfun : (fun y => χ s * χ (y - s)) = χ := by
    funext y
    rw [← hadd]
    congr 1
    ring
  rw [hfun] at hmul
  rw [mul_comm]
  exact hmul
end GlobalTheory.DerivativeOfAdditiveContinuous
