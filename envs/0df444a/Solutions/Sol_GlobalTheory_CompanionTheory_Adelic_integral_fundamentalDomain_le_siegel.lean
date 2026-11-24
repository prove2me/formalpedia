-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Adelic.integral_fundamentalDomain_le_siegel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:19:36.925525+00:00
-- url     : https://prove2.me/submissions/2b4d355b-c829-4804-abe5-376e0d6a8925

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_Nuabs
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InvariantMeasureCompactCoverBound
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_cover


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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Adelic
namespace GlobalTheory.CompanionTheory.Adelic
theorem _root_.solution : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (P : Subgroup G) (ν : Measure G) [SFinite ν], (∀ p ∈ P, ν.map (fun g => p * g) = ν) → (∀ U ∈ 𝓝 (1 : G), ν U ≠ 0) → ∀ C : Set G, IsCompact C → ∃ (C' : Set G) (K : ℝ≥0∞), IsCompact C' ∧ K < ⊤ ∧ ∀ (Γ : Subgroup G) [Countable Γ], Γ ≤ P → ∀ 𝓕 : Set G, IsFundamentalDomain Γ 𝓕 μ → ∀ S : Set G, MeasurableSet S → (∀ᵐ p ∂ν, ∃ γ ∈ Γ, γ * p ∈ S) → ∀ f g : G → ℝ≥0∞, Measurable f → Measurable g → (∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) → (∀ x, f x ≠ 0 → ∃ p ∈ P, ∃ c ∈ C, x = p * c) → (∀ p ∈ S, ∀ c ∈ C', f (p * c) ≤ g p) → ∫⁻ x in 𝓕, f x ∂μ ≤ K * ∫⁻ p in S, g p ∂ν := by
  first | exact CompanionTheory.PlacePermOperatorBicommutantSpan.cover | exact @CompanionTheory.PlacePermOperatorBicommutantSpan.cover
end GlobalTheory.CompanionTheory.Adelic
