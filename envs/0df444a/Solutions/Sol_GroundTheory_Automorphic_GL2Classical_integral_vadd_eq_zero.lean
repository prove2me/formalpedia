-- Prove2me | solution 1 for GroundTheory.Automorphic.GL2Classical.integral_vadd_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:43:21.901462+00:00
-- url     : https://prove2.me/submissions/9d117745-6b09-41dc-b48d-9f44852691bf

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2Classical_Periodic
import Theorems.Thm_GroundTheory_Automorphic_GL2Classical_integral_periodic_eq_of_im

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory intervalIntegral Filter Topology Set
open UpperHalfPlane hiding I I_re I_im
open scoped Manifold Interval
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.GL2Classical
namespace GroundTheory.Automorphic.GL2Classical
theorem _root_.solution {F : ℍ → ℂ} (hF : MDiff F) {T : ℝ} (hT : 0 < T)
    (hper : ∀ z : ℍ, F (T +ᵥ z) = F z) (hzero : IsZeroAtImInfty F) (z : ℍ) :
    ∫ t in (0 : ℝ)..T, F (t +ᵥ z) = 0 := by
  set G : ℂ → ℂ := F ∘ ofComplex
  have hG : DifferentiableOn ℂ G {w | 0 < w.im} := mdifferentiable_iff.1 hF
  have hGw : ∀ w : ℂ, (hw : 0 < w.im) → G w = F ⟨w, hw⟩ := fun w hw => by
    simp only [G, Function.comp_apply, ofComplex_apply_of_im_pos hw]
  have hper' : ∀ w : ℂ, 0 < w.im → G (w + T) = G w := fun w hw => by
    have hw' : 0 < (w + T).im := by simpa using hw
    rw [hGw _ hw', hGw _ hw, ← hper ⟨w, hw⟩]
    congr 1
    ext
    simp [coe_vadd, add_comm]

  have hint : ∀ y : ℝ, 0 < y → ∫ t in (0 : ℝ)..T, G ((t + z.re : ℝ) + y * I) =
      ∫ x in z.re..z.re + T, G (x + y * I) := by
    intro y _
    have := intervalIntegral.integral_comp_add_right (fun x : ℝ => G (x + y * I)) z.re (a := 0) (b := T)
    simp only [zero_add] at this
    rw [add_comm z.re T]
    exact this
  have hzint : ∫ t in (0 : ℝ)..T, F (t +ᵥ z) = ∫ x in z.re..z.re + T, G (x + z.im * I) := by
    rw [← hint z.im z.im_pos]
    refine intervalIntegral.integral_congr fun t _ => ?_
    have him : 0 < (((t + z.re : ℝ) : ℂ) + z.im * I).im := by simpa using z.im_pos
    rw [hGw _ him]
    congr 1
    ext
    simp only [coe_vadd, ofReal_add]
    rw [add_assoc]
    exact congrArg _ (Complex.re_add_im (z : ℂ)).symm
  rw [hzint]

  refine norm_le_zero_iff.1 (le_of_forall_pos_le_add fun ε hε => ?_)
  rw [zero_add]
  obtain ⟨A, hA⟩ := (atImInfty_mem _).1 (hzero.eventually (Metric.closedBall_mem_nhds 0
    (div_pos hε hT)))
  set Y := max A 1 + z.im
  have hY : 0 < Y := by positivity
  rw [integral_periodic_eq_of_im hG hper' z.re z.im_pos hY]
  have hbound : ∀ x ∈ Set.uIoc z.re (z.re + T), ‖G (x + Y * I)‖ ≤ ε / T := by
    intro x _
    have him : 0 < ((x : ℂ) + Y * I).im := by simpa using hY
    rw [hGw _ him]
    have := hA ⟨_, him⟩ (by
      show A ≤ ((x : ℂ) + Y * I).im
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, zero_add]
      have := z.im_pos
      have : A ≤ max A 1 := le_max_left _ _
      linarith)
    simpa [Metric.mem_closedBall, dist_zero_right] using this
  calc ‖∫ x in z.re..z.re + T, G (x + Y * I)‖ ≤ ε / T * |z.re + T - z.re| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hbound
    _ = ε := by
        rw [add_sub_cancel_left, abs_of_pos hT]
        field_simp
end GroundTheory.Automorphic.GL2Classical
