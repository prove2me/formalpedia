-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HolMean.series_step
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:18:30.36981+00:00
-- url     : https://prove2.me/submissions/0525d246-0b6d-4284-b3d2-d8a44546b400

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AesmIteratedDerivReal
import Theorems.Thm_GlobalTheory_CompanionTheory_HolMean_cauchy_nhds

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
variable {κ : Type} {U : Set ℂ}
namespace GlobalTheory.CompanionTheory.HolMean
theorem _root_.solution (hU : IsOpen U) (F : κ → ℂ → ℂ) (hF : ∀ k, DifferentiableOn ℂ (F k) U)
    (hb : ∀ z₀ ∈ U, ∃ V ∈ 𝓝 z₀, ∃ u : κ → ℝ, Summable u ∧ ∀ z ∈ V ∩ U, ∀ k, ‖F k z‖ ≤ u k) :
    DifferentiableOn ℂ (fun w => ∑' k, F k w) U ∧
    (∀ z ∈ U, deriv (fun w => ∑' k, F k w) z = ∑' k, deriv (F k) z) ∧
    (∀ z₀ ∈ U, ∃ V ∈ 𝓝 z₀, ∃ u : κ → ℝ, Summable u ∧ ∀ z ∈ V ∩ U, ∀ k, ‖deriv (F k) z‖ ≤ u k) := by
  have key : ∀ z₀ ∈ U, ∃ ε > 0, Metric.ball z₀ ε ⊆ U ∧ ∃ u : κ → ℝ, Summable u ∧
      ∀ z ∈ Metric.ball z₀ ε, ∀ k, ‖F k z‖ ≤ u k := by
    intro z₀ hz₀
    obtain ⟨V, hV, u, hu, hle⟩ := hb z₀ hz₀
    obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hV (hU.mem_nhds hz₀))
    exact ⟨ε, hε, fun z hz => (hεs hz).2, u, hu, fun z hz k => hle z (hεs hz) k⟩
  refine ⟨?_, ?_, ?_⟩
  · intro z₀ hz₀
    obtain ⟨ε, hε, hsub, u, hu, hle⟩ := key z₀ hz₀
    have hd := Complex.differentiableOn_tsum_of_summable_norm hu (fun k => (hF k).mono hsub)
      Metric.isOpen_ball (fun k w hw => hle w hw k)
    exact (hd.differentiableAt (Metric.ball_mem_nhds z₀ hε)).differentiableWithinAt
  · intro z₀ hz₀
    obtain ⟨ε, hε, hsub, u, hu, hle⟩ := key z₀ hz₀
    exact (Complex.hasSum_deriv_of_summable_norm hu (fun k => (hF k).mono hsub) Metric.isOpen_ball
      (fun k w hw => hle w hw k) (Metric.mem_ball_self hε)).tsum_eq.symm
  · intro z₀ hz₀
    obtain ⟨V, hV, u, hu, hle⟩ := hb z₀ hz₀
    obtain ⟨R, hR, W, hW, hWU, hest⟩ := cauchy_nhds hU hz₀ hV
    refine ⟨W, hW, fun k => u k / R, hu.div_const R, ?_⟩
    intro z hz k
    exact hest (F k) (hF k) (u k) (fun w hw => hle w hw k) z hz.1
end GlobalTheory.CompanionTheory.HolMean
