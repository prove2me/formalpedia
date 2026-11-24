-- Prove2me | solution 1 for GlobalTheory.T.parabolic_haar_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:19:39.520797+00:00
-- url     : https://prove2.me/submissions/83ddded1-d5f5-42df-bdca-ee57c6ad4b04

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ParabolicHaarDecomposition
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SplitHomeoApply
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ParabolicHaarDecompositionStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SplitExtLat_conj_haar_character


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
theorem _root_.solution : ∀ (P G₁ : Type) [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [LocallyCompactSpace P] [SecondCountableTopology P] [T2Space P] [MeasurableSpace P] [BorelSpace P] [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁] (ι : G₁ →* P) (π : P →* G₁) (hι : Continuous ι) (hπ : Continuous π) (hπι : ∀ u, π (ι u) = u) (Γ : Subgroup P) (Γ₁ : Subgroup G₁) [Countable Γ] [Countable Γ₁], (∀ u ∈ Γ₁, ι u ∈ Γ) → ∀ (ν : Measure π.ker) [ν.IsHaarMeasure] (D : Set π.ker), MeasurableSet D → IsFundamentalDomain (Γ.subgroupOf π.ker) D ν → ν D ≠ 0 → ν D < ⊤ → ∃ δ : G₁ →* ℝ≥0, Measurable δ ∧ (∀ γ ∈ Γ₁, δ γ = 1) ∧ ∀ u, Measure.map (fun m : π.ker => MulAut.conjNormal (ι u) m) ν = δ u • ν := by
  first | exact @GlobalTheory.CompanionTheory.SplitExtLat.conj_haar_character | exact GlobalTheory.CompanionTheory.SplitExtLat.conj_haar_character | (intros; apply GlobalTheory.CompanionTheory.SplitExtLat.conj_haar_character <;> assumption)
end _root_.GlobalTheory.T
