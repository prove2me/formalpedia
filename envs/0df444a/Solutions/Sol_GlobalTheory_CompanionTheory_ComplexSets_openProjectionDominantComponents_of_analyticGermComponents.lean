-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ComplexSets.openProjectionDominantComponents_of_analyticGermComponents
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:55:27.447224+00:00
-- url     : https://prove2.me/submissions/1db54c37-46c2-4ca8-9ed9-bf7a42dd299c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StOpenProjectionDominantComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticGermComponents
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DominantComponentsOfGerm
import Theorems.Thm_GlobalTheory_CompanionTheory_ComplexSets_exists_subfamily_no_containment
import Theorems.Thm_GlobalTheory_CompanionTheory_ComplexSets_dominant_of_open

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
theorem _root_.solution :
    AnalyticGermComponents.Statement → OpenProjectionDominantComponents.Statement := by
  intro hAGC
  unfold AnalyticGermComponents.Statement at hAGC
  unfold OpenProjectionDominantComponents.Statement
  intro σ _ X B k f d A hB hf hXB hopen w hw
  have hAN : IsAnalyticNear (X ∩ B) w := by
    unfold IsAnalyticNear
    exact ⟨B, k, f, hB, hw.2, hf, by rw [Set.inter_assoc, Set.inter_self, hXB]⟩
  obtain ⟨n₀, Y₀, hY₀, W, hW, hXW⟩ := hAGC σ (X ∩ B) w hAN hw
  obtain ⟨T, hT, hTno⟩ := exists_subfamily_no_containment Y₀ w
  let e : Fin T.card ≃ T := T.equivFin.symm
  have hno : ∀ i j : Fin T.card, i ≠ j → ¬ ∀ᶠ z in 𝓝 w, z ∈ Y₀ (e i) → z ∈ Y₀ (e j) := by
    intro i j hij
    exact hTno _ (e i).2 _ (e j).2 (fun h => hij (e.injective (Subtype.ext h)))
  have hW' : W ∩ {z | z ∈ (⋃ i, Y₀ i) ↔ ∃ i ∈ T, z ∈ Y₀ i} ∈ 𝓝 w := Filter.inter_mem hW hT
  have hS : X ∩ B ∩ (W ∩ {z | z ∈ (⋃ i, Y₀ i) ↔ ∃ i ∈ T, z ∈ Y₀ i}) =
      (⋃ i, Y₀ (e i)) ∩ (W ∩ {z | z ∈ (⋃ i, Y₀ i) ↔ ∃ i ∈ T, z ∈ Y₀ i}) := by
    ext z
    constructor
    · rintro ⟨hzXB, hzW, hzT⟩
      have h1 : z ∈ (⋃ i, Y₀ i) ∩ W := by rw [← hXW]; exact ⟨hzXB, hzW⟩
      obtain ⟨i, hiT, hzi⟩ := hzT.mp h1.1
      refine ⟨Set.mem_iUnion.mpr ⟨e.symm ⟨i, hiT⟩, ?_⟩, hzW, hzT⟩
      simpa using hzi
    · rintro ⟨hzU, hzW, hzT⟩
      obtain ⟨i, hzi⟩ := Set.mem_iUnion.mp hzU
      have h1 : z ∈ (⋃ i, Y₀ i) ∩ W := ⟨Set.mem_iUnion.mpr ⟨_, hzi⟩, hzW⟩
      rw [← hXW] at h1
      exact ⟨h1.1, hzW, hzT⟩
  refine ⟨T.card, fun i => Y₀ (e i), fun i => ⟨(hY₀ _).1, (hY₀ _).2, fun h hh hv => ?_⟩, hno,
    _, hW', hS⟩
  exact dominant_of_open A (fun j => Y₀ (e j)) hopen (fun j => (hY₀ _).1) (fun j => (hY₀ _).2)
    hno hW' hS i h hh hv
end GlobalTheory.CompanionTheory.ComplexSets
