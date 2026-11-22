-- Prove2me | solution 1 for Kyprianou.Ch02.abstractPRMDisjointSigmaIndepV8
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T22:55:36.582048+00:00
-- url     : https://prove2.me/submissions/007d2fe2-c7db-4b48-866b-aebde7eb7aa8

import Mathlib
import Theorems.Thm_LevyStochCalc_Poisson_indep_of_disjoint_region_families_ch02
import Theorems.Thm_LevyStochCalc_Probability_indep_iSup_of_finset_readable
import Definitions.Def_Kyprianou_Ch02_AbstractPoissonRandomMeasureV8
open MeasureTheory ProbabilityTheory Kyprianou.Ch02
open scoped NNReal ENNReal
set_option autoImplicit false


theorem solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m]
    (N : Ω → Measure E)
    (hN : Kyprianou.Ch02.IsAbstractPoissonRandomMeasureCh02V8 P m N) :
    ∀ (A B : Set E),
      MeasurableSet A → MeasurableSet B → Disjoint A B →
      ProbabilityTheory.Indep
        (⨆ C ∈ {C : Set E | C ⊆ A ∧ MeasurableSet C},
           MeasurableSpace.comap (fun ω => N ω C) inferInstance)
        (⨆ D ∈ {D : Set E | D ⊆ B ∧ MeasurableSet D},
           MeasurableSpace.comap (fun ω => N ω D) inferInstance)
        P := by
  classical
  rcases hN with ⟨⟨hmeas, _, _, _, hind⟩, _⟩
  intro A B hA hB hAB
  let ℬ : Set (Set E) := {D | D ⊆ B ∧ MeasurableSet D}
  let 𝒞 : Set (Set E) := {C | C ⊆ A ∧ MeasurableSet C}
  have hmeas' : ∀ {D : Set E}, MeasurableSet D →
      Measurable (fun ω => N ω D) := by
    intro D hD
    exact hmeas D hD
  have hind' : ∀ {ι : Type} [Countable ι] (D : ι → Set E),
      (∀ i, MeasurableSet (D i)) →
      Pairwise (fun i j => Disjoint (D i) (D j)) →
      ProbabilityTheory.iIndepFun (fun i ω => N ω (D i)) P := by
    intro ι inst D hD hdisj
    exact hind D hD hdisj
  have h𝒞le :
      (⨆ C ∈ 𝒞, MeasurableSpace.comap
        (fun ω => N ω C) inferInstance) ≤
      (inferInstance : MeasurableSpace Ω) := by
    exact iSup₂_le fun C hC => (hmeas' hC.2).comap_le
  have hInd :
      ProbabilityTheory.Indep
        (⨆ D : ℬ, MeasurableSpace.comap
          (fun ω => N ω (D : Set E)) inferInstance)
        (⨆ C ∈ 𝒞, MeasurableSpace.comap
          (fun ω => N ω C) inferInstance) P := by
    refine LevyStochCalc.Probability.indep_iSup_of_finset_readable
      (fun D => (hmeas' D.2.2).comap_le) h𝒞le ?_
    intro S
    let fam : Fin S.card → Set E :=
      fun i => (S.equivFin.symm i).1.1
    have hfam : ∀ i, MeasurableSet (fam i) :=
      fun i => (S.equivFin.symm i).1.2.2
    have hsmall :=
      LevyStochCalc.Poisson.indep_of_disjoint_region_families_ch02
        (P := P) (N := N) hmeas' hind' fam hfam
    refine indep_of_indep_of_le_right
      (indep_of_indep_of_le_left hsmall.symm ?_) ?_
    · refine iSup₂_le fun D hD => le_iSup_of_le
        (S.equivFin ⟨D, hD⟩) ?_
      simp [fam]
    · refine iSup₂_le fun C hC =>
        le_iSup₂_of_le C ?_ le_rfl
      refine ⟨?_, hC.2⟩
      intro j
      exact hAB.mono hC.1 (S.equivFin.symm j).1.2.1
  have hℬ :
      (⨆ D : ℬ, MeasurableSpace.comap
        (fun ω => N ω (D : Set E)) inferInstance) =
      (⨆ D ∈ ℬ, MeasurableSpace.comap
        (fun ω => N ω D) inferInstance) := by
    apply le_antisymm
    · exact iSup_le fun D => le_iSup₂_of_le
        (D : Set E) D.2 le_rfl
    · exact iSup₂_le fun D hD => le_iSup_of_le
        (⟨D, hD⟩ : ℬ) le_rfl
  rw [hℬ] at hInd
  simpa only [𝒞, ℬ] using hInd.symm

