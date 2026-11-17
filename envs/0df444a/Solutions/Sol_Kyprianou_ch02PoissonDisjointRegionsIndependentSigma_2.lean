-- Prove2me | solution 2 for Kyprianou.ch02PoissonDisjointRegionsIndependentSigma
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:56:02.757179+00:00
-- url     : https://prove2.me/submissions/c59fd662-adcf-4346-84b0-8ef0807d3122

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Theorems.Thm_LevyStochCalc_Poisson_indep_of_disjoint_region_families_ch02
import Theorems.Thm_LevyStochCalc_Probability_indep_iSup_of_finset_readable
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true


theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν) :
    (∀ (A B : Set (ℝ × ℝ)), MeasurableSet A →
      MeasurableSet B → Disjoint A B →
      ProbabilityTheory.Indep
        (⨆ C ∈ {C : Set (ℝ × ℝ) |
             C ⊆ A ∧ MeasurableSet C},
          MeasurableSpace.comap (fun ω => N.N ω C) inferInstance)
        (⨆ D ∈ {D : Set (ℝ × ℝ) |
             D ⊆ B ∧ MeasurableSet D},
          MeasurableSpace.comap (fun ω => N.N ω D) inferInstance)
        P) := by
  intro A B hA hB hAB
  classical
  let ℬ : Set (Set (ℝ × ℝ)) :=
    {D | D ⊆ B ∧ MeasurableSet D}
  let 𝒞 : Set (Set (ℝ × ℝ)) :=
    {C | C ⊆ A ∧ MeasurableSet C}
  have hmeas :
      ∀ {D : Set (ℝ × ℝ)}, MeasurableSet D →
        Measurable (fun ω => N.N ω D) := by
    intro D hD
    exact N.measurable_eval hD
  have hind :
      ∀ {ι : Type} [Countable ι] (D : ι → Set (ℝ × ℝ)),
        (∀ i, MeasurableSet (D i)) →
        Pairwise (fun i j => Disjoint (D i) (D j)) →
        ProbabilityTheory.iIndepFun
          (fun i ω => N.N ω (D i)) P := by
    intro ι inst D hD hdisj
    exact LevyStochCalc.Poisson.PoissonRandomMeasure.independent_disjoint.{0,0,0} N D hD hdisj
  have h𝒞le :
      (⨆ C ∈ 𝒞, MeasurableSpace.comap
        (fun ω => N.N ω C) inferInstance) ≤
      (inferInstance : MeasurableSpace Ω) := by
    exact iSup₂_le fun C hC => (hmeas hC.2).comap_le
  have hInd :
      ProbabilityTheory.Indep
        (⨆ D : ℬ, MeasurableSpace.comap
          (fun ω => N.N ω (D : Set (ℝ × ℝ))) inferInstance)
        (⨆ C ∈ 𝒞, MeasurableSpace.comap
          (fun ω => N.N ω C) inferInstance) P := by
    refine LevyStochCalc.Probability.indep_iSup_of_finset_readable
      (fun D => (hmeas D.2.2).comap_le) h𝒞le ?_
    intro S
    let fam : Fin S.card → Set (ℝ × ℝ) :=
      fun i => (S.equivFin.symm i).1.1
    have hfam : ∀ i, MeasurableSet (fam i) :=
      fun i => (S.equivFin.symm i).1.2.2
    have hsmall :=
      LevyStochCalc.Poisson.indep_of_disjoint_region_families_ch02
        (P := P) (N := N.N) hmeas hind fam hfam
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
        (fun ω => N.N ω (D : Set (ℝ × ℝ))) inferInstance) =
      (⨆ D ∈ ℬ, MeasurableSpace.comap
        (fun ω => N.N ω D) inferInstance) := by
    apply le_antisymm
    · exact iSup_le fun D => le_iSup₂_of_le
        (D : Set (ℝ × ℝ)) D.2 le_rfl
    · exact iSup₂_le fun D hD => le_iSup_of_le
        (⟨D, hD⟩ : ℬ) le_rfl
  rw [hℬ] at hInd
  simpa only [𝒞, ℬ] using hInd.symm

