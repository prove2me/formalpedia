-- Prove2me | solution 1 for GlobalTheory.T.fundamental_domain_of_subgroup_from_coset_reps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:10:51.815832+00:00
-- url     : https://prove2.me/submissions/26a154d5-8d1b-46da-aa4e-56584f324dea

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FundamentalDomainOfSubgroupFromCosetReps
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FundamentalDomainOfSubgroupFromCosetRepsStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Adelic_unfold_coset_sum_fundamentalDomain


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (Γ Γ' : Subgroup G) [Countable Γ], Γ' ≤ Γ → ∀ 𝓕 : Set G, IsFundamentalDomain Γ 𝓕 μ → ∀ (Q : Type) (r : Q → G), (∀ q, r q ∈ Γ) → (∀ γ ∈ Γ, ∃! q, γ * (r q)⁻¹ ∈ Γ') → ∃ 𝓕' : Set G, IsFundamentalDomain Γ' 𝓕' μ ∧ ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ h in 𝓕, ∑' q, f (r q * h) ∂μ = ∫⁻ h in 𝓕', f h ∂μ := by
  first | exact @GlobalTheory.CompanionTheory.Adelic.unfold_coset_sum_fundamentalDomain | exact GlobalTheory.CompanionTheory.Adelic.unfold_coset_sum_fundamentalDomain | (intros; apply GlobalTheory.CompanionTheory.Adelic.unfold_coset_sum_fundamentalDomain <;> assumption)
end _root_.GlobalTheory.T
