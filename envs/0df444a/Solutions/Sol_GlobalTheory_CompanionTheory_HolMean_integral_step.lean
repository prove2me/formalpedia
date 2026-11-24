-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HolMean.integral_step
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:18:26.434333+00:00
-- url     : https://prove2.me/submissions/a52ccd2f-8bcb-45ec-8c20-cac4c610c173

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AesmIteratedDerivReal
import Theorems.Thm_GlobalTheory_CompanionTheory_HolMean_cauchy_nhds
import Theorems.Thm_GlobalTheory_CompanionTheory_HolMean_aesm_deriv

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
variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} {U : Set ℂ}
namespace GlobalTheory.CompanionTheory.HolMean
theorem _root_.solution (hU : IsOpen U) (G : ℂ → Ω → ℂ)
    (hd : ∀ ω, DifferentiableOn ℂ (fun z => G z ω) U)
    (hm : ∀ z ∈ U, AEStronglyMeasurable (G z) μ)
    (hb : ∀ z₀ ∈ U, ∃ V ∈ 𝓝 z₀, ∃ g : Ω → ℝ, Integrable g μ ∧ ∀ z ∈ V ∩ U, ∀ ω, ‖G z ω‖ ≤ g ω) :
    (∀ z ∈ U, HasDerivAt (fun w => ∫ ω, G w ω ∂μ) (∫ ω, deriv (fun w => G w ω) z ∂μ) z) ∧
    (∀ z ∈ U, AEStronglyMeasurable (fun ω => deriv (fun w => G w ω) z) μ) ∧
    (∀ z₀ ∈ U, ∃ V ∈ 𝓝 z₀, ∃ g : Ω → ℝ, Integrable g μ ∧
      ∀ z ∈ V ∩ U, ∀ ω, ‖deriv (fun w => G w ω) z‖ ≤ g ω) := by
  have h2 : ∀ z ∈ U, AEStronglyMeasurable (fun ω => deriv (fun w => G w ω) z) μ :=
    fun z hz => aesm_deriv hU G hd hz (fun x hx => hm _ hx)
  have h3 : ∀ z₀ ∈ U, ∃ V ∈ 𝓝 z₀, ∃ g : Ω → ℝ, Integrable g μ ∧
      ∀ z ∈ V ∩ U, ∀ ω, ‖deriv (fun w => G w ω) z‖ ≤ g ω := by
    intro z₀ hz₀
    obtain ⟨V, hV, g, hg, hle⟩ := hb z₀ hz₀
    obtain ⟨R, hR, W, hW, hWU, hest⟩ := cauchy_nhds hU hz₀ hV
    refine ⟨W, hW, fun ω => g ω / R, hg.div_const R, ?_⟩
    intro z hz ω
    exact hest (fun w => G w ω) (hd ω) (g ω) (fun w hw => hle w hw ω) z hz.1
  refine ⟨?_, h2, h3⟩
  intro z hz
  obtain ⟨V, hV, g, hg, hle⟩ := hb z hz
  obtain ⟨W, hW, g', hg', hle'⟩ := h3 z hz
  obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hW (hU.mem_nhds hz))
  have hint : Integrable (G z) μ :=
    hg.mono' (hm z hz) (ae_of_all μ fun ω => hle z ⟨mem_of_mem_nhds hV, hz⟩ ω)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := G) (F' := fun x ω => deriv (fun w => G w ω) x) (bound := g') (Metric.ball_mem_nhds z hε)
    (Filter.eventually_of_mem (hU.mem_nhds hz) hm) hint (h2 z hz)
    (ae_of_all μ fun ω x hx => hle' x (hεs hx) ω) hg'
    (ae_of_all μ fun ω x hx =>
      (((hd ω) x (hεs hx).2).differentiableAt (hU.mem_nhds (hεs hx).2)).hasDerivAt)).2
end GlobalTheory.CompanionTheory.HolMean
