-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ComplexSets.exists_subfamily_no_containment
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:24:33.637543+00:00
-- url     : https://prove2.me/submissions/fe21ad23-f982-4945-aeb3-694377af59e3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StOpenProjectionDominantComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticGermComponents
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DominantComponentsOfGerm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets Topology Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ComplexSets
variable {σ : Type} [Fintype σ]
namespace GlobalTheory.CompanionTheory.ComplexSets
theorem _root_.solution {ι : Type} [Finite ι] (Y : ι → Set (σ → ℂ)) (w : σ → ℂ) :
    ∃ T : Finset ι, (∀ᶠ z in 𝓝 w, z ∈ (⋃ i, Y i) ↔ ∃ i ∈ T, z ∈ Y i) ∧
      ∀ i ∈ T, ∀ j ∈ T, i ≠ j → ¬ ∀ᶠ z in 𝓝 w, z ∈ Y i → z ∈ Y j := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  let P : Finset ι → Prop := fun T => ∀ᶠ z in 𝓝 w, z ∈ (⋃ i, Y i) ↔ ∃ i ∈ T, z ∈ Y i
  have hP : P Finset.univ := Filter.Eventually.of_forall fun z => by simp
  obtain ⟨T, hT, hmin⟩ := Finset.exists_min_image (Finset.univ.filter P) Finset.card
    ⟨Finset.univ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hP⟩⟩
  rw [Finset.mem_filter] at hT
  refine ⟨T, hT.2, ?_⟩
  intro i hi j hj hij hsub
  have hP' : P (T.erase i) := by
    filter_upwards [hT.2, hsub] with z hz hzs
    rw [hz]
    constructor
    · rintro ⟨m, hm, hzm⟩
      by_cases hmi : m = i
      · rw [hmi] at hzm
        exact ⟨j, Finset.mem_erase.mpr ⟨Ne.symm hij, hj⟩, hzs hzm⟩
      · exact ⟨m, Finset.mem_erase.mpr ⟨hmi, hm⟩, hzm⟩
    · rintro ⟨m, hm, hzm⟩
      exact ⟨m, Finset.mem_of_mem_erase hm, hzm⟩
  have hle := hmin (T.erase i) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hP'⟩)
  have hlt := Finset.card_erase_lt_of_mem hi
  omega
end GlobalTheory.CompanionTheory.ComplexSets
