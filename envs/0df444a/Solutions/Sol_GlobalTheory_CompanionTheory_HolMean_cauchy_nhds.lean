-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HolMean.cauchy_nhds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:15:57.016445+00:00
-- url     : https://prove2.me/submissions/7b52ad69-a653-40e5-9bfa-04c3c41868e4

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AesmIteratedDerivReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HolMean
namespace GlobalTheory.CompanionTheory.HolMean
theorem _root_.solution {U V : Set ℂ} (hU : IsOpen U) {z₀ : ℂ} (hz₀ : z₀ ∈ U) (hV : V ∈ 𝓝 z₀) :
    ∃ R : ℝ, 0 < R ∧ ∃ W ∈ 𝓝 z₀, W ⊆ U ∧ ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U →
      ∀ C : ℝ, (∀ z ∈ V ∩ U, ‖f z‖ ≤ C) → ∀ z ∈ W, ‖deriv f z‖ ≤ C / R := by
  obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hV (hU.mem_nhds hz₀))
  refine ⟨ε / 2, half_pos hε, Metric.ball z₀ (ε / 2), Metric.ball_mem_nhds z₀ (half_pos hε), ?_, ?_⟩
  · intro z hz
    exact (hεs (Metric.ball_subset_ball (by linarith) hz)).2
  · intro f hf C hC z hz
    have hsub : Metric.closedBall z (ε / 2) ⊆ V ∩ U := by
      intro w hw
      apply hεs
      rw [Metric.mem_ball] at hz ⊢
      rw [Metric.mem_closedBall] at hw
      calc dist w z₀ ≤ dist w z + dist z z₀ := dist_triangle _ _ _
        _ < ε / 2 + ε / 2 := by linarith
        _ = ε := by ring
    apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (half_pos hε)
    · apply DifferentiableOn.diffContOnCl
      exact hf.mono (Metric.closure_ball_subset_closedBall.trans (hsub.trans Set.inter_subset_right))
    · intro w hw
      exact hC w (hsub (Metric.sphere_subset_closedBall hw))
end GlobalTheory.CompanionTheory.HolMean
