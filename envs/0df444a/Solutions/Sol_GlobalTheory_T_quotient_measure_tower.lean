-- Prove2me | solution 1 for GlobalTheory.T.quotient_measure_tower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:26:36.06903+00:00
-- url     : https://prove2.me/submissions/cd3d5bac-4a8b-4a31-b584-fb392c2b3fcf

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_QuotientMeasureTower
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_QuotientMeasureTowerStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Averaging_lintegral_sum_cosets_average


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (G₁ : Type) [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [MeasurableSpace G₁] [BorelSpace G₁] (ι : G₁ →* G), IsClosedEmbedding ι → ∀ (μ : Measure G) [μ.IsHaarMeasure] (μ₁ : Measure G₁) [μ₁.IsHaarMeasure] (Γ : Subgroup G) [Countable Γ] (Γ₁ : Subgroup G₁) [Countable Γ₁] (𝓕 : Set G) (𝓕₁ : Set G₁), IsFundamentalDomain Γ 𝓕 μ → IsFundamentalDomain Γ₁ 𝓕₁ μ₁ → μ₁ 𝓕₁ < ⊤ → (∀ u ∈ Γ₁, ι u ∈ Γ) → ∀ (Q : Type) [Countable Q] (r : Q → G), (∀ q, r q ∈ Γ) → (∀ γ ∈ Γ, ∃! q, ∃ u ∈ Γ₁, γ = ι u * r q) → ∀ φ : G → ℝ≥0∞, Measurable φ → (∀ u ∈ Γ₁, ∀ g, φ (ι u * g) = φ g) → ∫⁻ h in 𝓕, ∑' q, φ (r q * h) ∂μ = ∫⁻ h in 𝓕, ∑' q, (μ₁ 𝓕₁)⁻¹ * ∫⁻ u in 𝓕₁, φ (ι u * (r q * h)) ∂μ₁ ∂μ := by
  first | exact @GlobalTheory.CompanionTheory.SW.Averaging.lintegral_sum_cosets_average | exact GlobalTheory.CompanionTheory.SW.Averaging.lintegral_sum_cosets_average | (intros; apply GlobalTheory.CompanionTheory.SW.Averaging.lintegral_sum_cosets_average <;> assumption)
end _root_.GlobalTheory.T
