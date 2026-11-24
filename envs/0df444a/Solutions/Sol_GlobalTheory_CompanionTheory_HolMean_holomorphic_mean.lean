-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HolMean.holomorphic_mean
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:35:06.415553+00:00
-- url     : https://prove2.me/submissions/57454877-bc68-403e-9684-a94c46f6fc9d

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AesmIteratedDerivReal
import Theorems.Thm_GlobalTheory_CompanionTheory_HolMean_series_step
import Theorems.Thm_GlobalTheory_CompanionTheory_HolMean_iteratedDeriv_series
import Theorems.Thm_GlobalTheory_CompanionTheory_HolMean_aesm_of_real
import Theorems.Thm_GlobalTheory_CompanionTheory_HolMean_integral_step
import Theorems.Thm_GlobalTheory_CompanionTheory_HolMean_iteratedDeriv_integral

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
theorem _root_.solution (P Ω κ : Type) [TopologicalSpace P] [FirstCountableTopology P]
    [MeasurableSpace Ω] [Countable κ] (μ : Measure Ω) (U : Set ℂ)
    (hU : IsOpen U)
    (hball : ∀ z ∈ U, ∃ (t ρ : ℝ), 0 < ρ ∧ z ∈ Metric.ball (t : ℂ) ρ ∧ Metric.ball (t : ℂ) ρ ⊆ U)
    (F : P → ℂ → Ω → κ → ℂ) (hF : ∀ p ω k, DifferentiableOn ℂ (fun z => F p z ω k) U)
    (hFc : ∀ ω k, ContinuousOn (fun q : P × ℂ => F q.1 q.2 ω k) (Set.univ ×ˢ U))
    (hFm : ∀ p (t : ℝ), (t : ℂ) ∈ U → AEStronglyMeasurable (fun ω => ∑' k, F p t ω k) μ)
    (hB : ∀ q ∈ (Set.univ : Set P) ×ˢ U, ∃ N ∈ 𝓝 q, ∃ (M : Ω → κ → ℝ) (g : Ω → ℝ),
      (∀ ω, Summable (M ω)) ∧ Integrable g μ ∧ (∀ ω, ∑' k, M ω k ≤ g ω) ∧
      ∀ q' ∈ N, q'.2 ∈ U → ∀ ω k, ‖F q'.1 q'.2 ω k‖ ≤ M ω k) :
    ContinuousOn (fun q : P × ℂ => ∫ ω, ∑' k, F q.1 q.2 ω k ∂μ) (Set.univ ×ˢ U) ∧
      (∀ p, DifferentiableOn ℂ (fun z => ∫ ω, ∑' k, F p z ω k ∂μ) U) ∧
      ∀ p, ∀ z ∈ U, ∀ r : ℕ, iteratedDeriv r (fun z => ∫ ω, ∑' k, F p z ω k ∂μ) z =
        ∫ ω, ∑' k, iteratedDeriv r (fun z => F p z ω k) z ∂μ := by
  have hser : ∀ p ω, ∀ z₀ ∈ U, ∃ V ∈ 𝓝 z₀, ∃ u : κ → ℝ, Summable u ∧
      ∀ z ∈ V ∩ U, ∀ k, ‖F p z ω k‖ ≤ u k := by
    intro p ω z₀ hz₀
    obtain ⟨N, hN, M, g, hM, hg, hMg, hle⟩ := hB (p, z₀) ⟨Set.mem_univ _, hz₀⟩
    obtain ⟨A, hA, V, hV, hAV⟩ := mem_nhds_prod_iff.mp hN
    exact ⟨V, hV, M ω, hM ω, fun z hz k => hle (p, z) (hAV ⟨mem_of_mem_nhds hA, hz.1⟩) hz.2 ω k⟩
  have hdS : ∀ p ω, DifferentiableOn ℂ (fun z => ∑' k, F p z ω k) U := fun p ω =>
    (series_step hU (fun k z => F p z ω k) (fun k => hF p ω k) (hser p ω)).1
  have hmeas : ∀ p z, z ∈ U → AEStronglyMeasurable (fun ω => ∑' k, F p z ω k) μ :=
    fun p z hz => aesm_of_real hU hball (fun z ω => ∑' k, F p z ω k) (hdS p) (hFm p) hz
  have hint : ∀ p, ∀ z₀ ∈ U, ∃ V ∈ 𝓝 z₀, ∃ g : Ω → ℝ, Integrable g μ ∧
      ∀ z ∈ V ∩ U, ∀ ω, ‖∑' k, F p z ω k‖ ≤ g ω := by
    intro p z₀ hz₀
    obtain ⟨N, hN, M, g, hM, hg, hMg, hle⟩ := hB (p, z₀) ⟨Set.mem_univ _, hz₀⟩
    obtain ⟨A, hA, V, hV, hAV⟩ := mem_nhds_prod_iff.mp hN
    refine ⟨V, hV, g, hg, fun z hz ω => ?_⟩
    exact (tsum_of_norm_bounded (hM ω).hasSum
      (fun k => hle (p, z) (hAV ⟨mem_of_mem_nhds hA, hz.1⟩) hz.2 ω k)).trans (hMg ω)
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨N, hN, M, g, hM, hg, hMg, hle⟩ := hB q hq
    have hS : ∀ q' ∈ (Set.univ ×ˢ U) ∩ N, ∀ ω, ‖∑' k, F q'.1 q'.2 ω k‖ ≤ g ω := fun q' hq' ω =>
      (tsum_of_norm_bounded (hM ω).hasSum (fun k => hle q' hq'.2 hq'.1.2 ω k)).trans (hMg ω)
    refine continuousWithinAt_of_dominated (bound := g) ?_ ?_ hg ?_
    · exact Filter.eventually_of_mem self_mem_nhdsWithin (fun q' hq' => hmeas q'.1 q'.2 hq'.2)
    · exact Filter.eventually_of_mem (inter_mem_nhdsWithin _ hN)
        (fun q' hq' => ae_of_all μ (hS q' hq'))
    · refine ae_of_all μ fun ω => ?_
      have hc : ContinuousOn (fun q' : P × ℂ => ∑' k, F q'.1 q'.2 ω k) ((Set.univ ×ˢ U) ∩ N) :=
        continuousOn_tsum (fun k => (hFc ω k).mono Set.inter_subset_left) (hM ω)
          (fun k q' hq' => hle q' hq'.2 hq'.1.2 ω k)
      exact (continuousWithinAt_inter hN).mp (hc q ⟨hq, mem_of_mem_nhds hN⟩)
  · intro p z hz
    exact (((integral_step hU (fun z ω => ∑' k, F p z ω k) (hdS p) (fun z hz => hmeas p z hz)
      (hint p)).1 z hz).differentiableAt).differentiableWithinAt
  · intro p z hz r
    refine (iteratedDeriv_integral hU r (fun z ω => ∑' k, F p z ω k) (hdS p)
      (fun z hz => hmeas p z hz) (hint p) z hz).trans ?_
    congr 1
    funext ω
    exact iteratedDeriv_series hU r (fun k z => F p z ω k) (fun k => hF p ω k) (hser p ω) z hz
end GlobalTheory.CompanionTheory.HolMean
