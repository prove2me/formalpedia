-- Prove2me | solution 1 for GlobalTheory.SCV.differentiableOn_fderiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:02:36.307915+00:00
-- url     : https://prove2.me/submissions/8ff0fb6b-ec7d-4ed4-93ce-484b53989067

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Theorems.Thm_GlobalTheory_SCV_norm_sub_sub_fderiv_le_of_ball
import Theorems.Thm_GlobalTheory_SCV_tendstoUniformlyOn_fderiv_ball
import Theorems.Thm_GlobalTheory_SCV_exists_ball_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Set Filter
open scoped Topology ContDiff Nat
open GlobalTheory GlobalTheory.SCV
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace GlobalTheory.SCV
theorem _root_.solution [CompleteSpace V] {f : E → V} {U : Set E} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (v : E) :
    DifferentiableOn ℂ (fun x => fderiv ℂ f x v) U := by
  intro c hc
  obtain ⟨R, hR, M, hRU, hM⟩ := exists_ball_bound hU hf hc
  set r := R / 4 with hr
  have hr0 : 0 < r := by positivity
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM c (mem_ball_self hR))
  have hsub : ∀ x ∈ ball c (2 * r), ball x (2 * r) ⊆ ball c R := fun x hx =>
    ball_subset_ball' (by linarith [mem_ball.mp hx])
  have hsmall : ∀ᶠ t in 𝓝[≠] (0 : ℂ), ‖t • v‖ < 2 * r := by
    have : Tendsto (fun t : ℂ => ‖t • v‖) (𝓝 0) (𝓝 0) :=
      Continuous.tendsto' (by fun_prop) _ _ (by simp)
    exact nhdsWithin_le_nhds (this.eventually (gt_mem_nhds (by positivity)))
  have hmem : ∀ t : ℂ, ‖t • v‖ < 2 * r → ∀ x, x + t • v ∈ ball x (2 * r) := by
    intro t ht x
    simpa [mem_ball_iff_norm] using ht
  have key := tendstoUniformlyOn_fderiv_ball (l := 𝓝[≠] (0 : ℂ))
    (F := fun t x => t⁻¹ • (f (x + t • v) - f x)) (f := fun x => fderiv ℂ f x v) (c := c) (r := r)
    ?_ ?_
  · exact (key.1.differentiableAt (ball_mem_nhds c hr0)).differentiableWithinAt
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have h0 : Tendsto (fun t : ℂ => 4 * M * (‖v‖ / (2 * r)) ^ 2 * ‖t‖) (𝓝 0) (𝓝 0) :=
      Continuous.tendsto' (by fun_prop) _ _ (by simp)
    filter_upwards [hsmall, nhdsWithin_le_nhds (h0.eventually (gt_mem_nhds hε)),
      self_mem_nhdsWithin] with t ht hte ht0 x hx
    have ht0' : t ≠ 0 := ht0
    have h1 := norm_sub_sub_fderiv_le_of_ball (hf.mono ((hsub x hx).trans hRU))
      (fun z hz => hM z (hsub x hx hz)) (hmem t ht x)
    rw [add_sub_cancel_left, map_smul, norm_smul] at h1
    have h2 : t⁻¹ • (f (x + t • v) - f x) - fderiv ℂ f x v
        = t⁻¹ • (f (x + t • v) - f x - t • fderiv ℂ f x v) := by
      rw [smul_sub t⁻¹ (_ - _), inv_smul_smul₀ ht0']
    rw [dist_comm, dist_eq_norm, h2, norm_smul, norm_inv]
    have htp : 0 < ‖t‖ := norm_pos_iff.mpr ht0'
    refine lt_of_le_of_lt ?_ hte
    rw [inv_mul_le_iff₀ htp]
    refine h1.trans_eq ?_
    ring
  · filter_upwards [hsmall] with t ht
    refine DifferentiableOn.const_smul (DifferentiableOn.sub ?_ ?_) _
    · exact hf.comp (by fun_prop) fun x hx => hRU (hsub x hx (hmem t ht x))
    · exact hf.mono ((ball_subset_ball (by linarith)).trans hRU)
end GlobalTheory.SCV
