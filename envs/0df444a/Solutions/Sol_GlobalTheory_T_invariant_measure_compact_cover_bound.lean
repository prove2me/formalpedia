-- Prove2me | solution 1 for GlobalTheory.T.invariant_measure_compact_cover_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:14:56.21381+00:00
-- url     : https://prove2.me/submissions/cae2a848-78c1-4bf7-bfb4-668aca7bba31

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InvariantMeasureCompactCoverBound
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InvariantMeasureCompactCoverBoundStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Adelic_integral_fundamentalDomain_le_siegel


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
theorem _root_.solution : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (P : Subgroup G) (ν : Measure G) [SFinite ν], (∀ p ∈ P, ν.map (fun g => p * g) = ν) → (∀ U ∈ 𝓝 (1 : G), ν U ≠ 0) → ∀ C : Set G, IsCompact C → ∃ (C' : Set G) (K : ℝ≥0∞), IsCompact C' ∧ K < ⊤ ∧ ∀ (Γ : Subgroup G) [Countable Γ], Γ ≤ P → ∀ 𝓕 : Set G, IsFundamentalDomain Γ 𝓕 μ → ∀ S : Set G, MeasurableSet S → (∀ᵐ p ∂ν, ∃ γ ∈ Γ, γ * p ∈ S) → ∀ f g : G → ℝ≥0∞, Measurable f → Measurable g → (∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) → (∀ x, f x ≠ 0 → ∃ p ∈ P, ∃ c ∈ C, x = p * c) → (∀ p ∈ S, ∀ c ∈ C', f (p * c) ≤ g p) → ∫⁻ x in 𝓕, f x ∂μ ≤ K * ∫⁻ p in S, g p ∂ν := by
  first | exact @GlobalTheory.CompanionTheory.Adelic.integral_fundamentalDomain_le_siegel | exact GlobalTheory.CompanionTheory.Adelic.integral_fundamentalDomain_le_siegel | (intros; apply GlobalTheory.CompanionTheory.Adelic.integral_fundamentalDomain_le_siegel <;> assumption)
end _root_.GlobalTheory.T
