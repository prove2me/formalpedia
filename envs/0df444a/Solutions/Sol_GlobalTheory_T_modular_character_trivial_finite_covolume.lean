-- Prove2me | solution 1 for GlobalTheory.T.modular_character_trivial_finite_covolume
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:18:29.024287+00:00
-- url     : https://prove2.me/submissions/592ae560-9e0b-49f4-8e3b-b7be17c67811

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ModularCharacterTrivialFiniteCovolume
import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FiniteCovolumeUnimodular
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_QuotientMeasureTower
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ModularCharacterTrivialFiniteCovolumeStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_CharacterTrivial_eq_one_of_isFundamentalDomain


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix Pointwise
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (G₁ : Type) [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁] (Γ₁ : Subgroup G₁) [Countable Γ₁] (μ₁ : Measure G₁) [μ₁.IsHaarMeasure] (𝓕₁ : Set G₁), IsFundamentalDomain Γ₁ 𝓕₁ μ₁ → μ₁ 𝓕₁ < ⊤ → ∀ δ : G₁ →* ℝ≥0, Measurable δ → (∀ γ ∈ Γ₁, δ γ = 1) → ∀ u, δ u = 1 := by
  first | exact @GlobalTheory.CompanionTheory.SW.CharacterTrivial.eq_one_of_isFundamentalDomain | exact GlobalTheory.CompanionTheory.SW.CharacterTrivial.eq_one_of_isFundamentalDomain | (intros; apply GlobalTheory.CompanionTheory.SW.CharacterTrivial.eq_one_of_isFundamentalDomain <;> assumption)
end _root_.GlobalTheory.T
