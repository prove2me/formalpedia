-- Prove2me | solution 1 for GlobalTheory.exists_circle_ne_zero_of_frequently_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:17:58.713633+00:00
-- url     : https://prove2.me/submissions/c63c4e33-faff-4fd0-932a-b0ab360b8d33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FderivIntegralApplyOfHolomorphicOfDominated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DifferentiableOnQuotientOfDifferentiableOnSlice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Metric Set
open scoped Topology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {S : Set E} {g : E → ℂ} {z₀ : E} (hS : S ∈ 𝓝 z₀)
    (hg : DifferentiableOn ℂ g S) (hfr : ∃ᶠ z in 𝓝 z₀, g z ≠ 0) :
    ∃ (v : E) (r : ℝ), 0 < r ∧ (∀ t ∈ closedBall (0 : ℂ) r, z₀ + t • v ∈ S) ∧
      ∀ t ∈ sphere (0 : ℂ) r, g (z₀ + t • v) ≠ 0 := by
  obtain ⟨ε, hε, hεS⟩ := Metric.mem_nhds_iff.1 hS
  obtain ⟨z₁, hz₁, hz₁b⟩ := (hfr.and_eventually (ball_mem_nhds z₀ (half_pos hε))).exists
  have hv : ‖z₁ - z₀‖ < ε / 2 := by simpa [dist_eq_norm] using hz₁b
  have hmem : ∀ t ∈ ball (0 : ℂ) 2, z₀ + t • (z₁ - z₀) ∈ S := by
    intro t ht
    apply hεS
    rw [mem_ball_zero_iff] at ht
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
    nlinarith [norm_nonneg t, norm_nonneg (z₁ - z₀)]
  have hd : DifferentiableOn ℂ (fun t : ℂ => g (z₀ + t • (z₁ - z₀))) (ball 0 2) :=
    hg.comp (f := fun t : ℂ => z₀ + t • (z₁ - z₀)) (by fun_prop) hmem
  have han := hd.analyticOnNhd isOpen_ball
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) 2 := by simp
  rcases (han 0 h0).eventually_eq_zero_or_eventually_ne_zero with h | h
  · have := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball 0 2).isPreconnected
      h0 h (show (1 : ℂ) ∈ ball (0 : ℂ) 2 by simp)
    exact absurd (by simpa using this) hz₁
  · rw [eventually_nhdsWithin_iff] at h
    obtain ⟨r, hr, hrs⟩ := nhds_basis_closedBall.mem_iff.1
      (h.and (ball_mem_nhds (0 : ℂ) two_pos))
    refine ⟨z₁ - z₀, r, hr, fun t ht => hmem t (hrs ht).2, fun t ht => ?_⟩
    refine (hrs (sphere_subset_closedBall ht)).1 ?_
    rintro rfl
    simp at ht
    exact hr.ne ht
end GlobalTheory
