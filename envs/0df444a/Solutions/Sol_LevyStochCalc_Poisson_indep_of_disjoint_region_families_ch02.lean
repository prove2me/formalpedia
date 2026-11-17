-- Prove2me | solution 1 for LevyStochCalc.Poisson.indep_of_disjoint_region_families_ch02
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T00:05:55.522524+00:00
-- url     : https://prove2.me/submissions/640cf784-6289-4388-901f-e2a288f4dd35

import Mathlib
import Definitions.Def_Kyprianou_Ch02_PartitionAtomV2
import Theorems.Thm_LevyStochCalc_Poisson_indep_iSup_comap_of_disjoint_families_ch02
import Theorems.Thm_LevyStochCalc_Probability_indep_iSup_of_finset_readable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson
set_option autoImplicit false
universe u v

theorem solution
    {Ω : Type u} [MeasurableSpace Ω]
  {𝓨 : Type v} [MeasurableSpace 𝓨]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {N : Ω → Measure 𝓨}
    (hN_meas : ∀ {B : Set 𝓨}, MeasurableSet B → Measurable (fun ω => N ω B))
    (hN_indep : ∀ {ι : Type} [Countable ι] (B : ι → Set 𝓨), (∀ i, MeasurableSet (B i)) →
      Pairwise (fun i j => Disjoint (B i) (B j)) → iIndepFun (fun i ω => N ω (B i)) P)
    {p : ℕ} (D : Fin p → Set 𝓨) (hD : ∀ j, MeasurableSet (D j)) :
    Indep (⨆ C ∈ {C : Set 𝓨 | (∀ j, Disjoint C (D j)) ∧ MeasurableSet C},
        MeasurableSpace.comap (fun ω => N ω C) inferInstance)
      (⨆ j, MeasurableSpace.comap (fun ω => N ω (D j)) inferInstance) P := by
  classical
  set 𝒞 := {C : Set 𝓨 | (∀ j, Disjoint C (D j)) ∧ MeasurableSet C} with h𝒞
  have hleft : (⨆ C ∈ 𝒞, MeasurableSpace.comap (fun ω => N ω C) inferInstance)
      = ⨆ C : 𝒞, MeasurableSpace.comap (fun ω => N ω (C : Set 𝓨)) inferInstance :=
    le_antisymm
      (iSup₂_le fun C hC => le_iSup (fun C : 𝒞 =>
        MeasurableSpace.comap (fun ω => N ω (C : Set 𝓨)) inferInstance) ⟨C, hC⟩)
      (iSup_le fun C => le_iSup₂_of_le (C : Set 𝓨) C.2 le_rfl)
  rw [hleft]
  refine LevyStochCalc.Probability.indep_iSup_of_finset_readable (fun C => (hN_meas C.2.2).comap_le)
    (iSup_le fun j => (hN_meas (hD j)).comap_le) fun S => ?_
  refine indep_of_indep_of_le_left
    (indep_iSup_comap_of_disjoint_families_ch02 hN_meas hN_indep
      (fun i : Fin S.card => ((S.equivFin.symm i : 𝒞) : Set 𝓨)) D
      (fun i => (S.equivFin.symm i).1.2.2) hD
      (fun i j => (S.equivFin.symm i).1.2.1 j)) ?_
  refine iSup₂_le fun C hC => le_iSup_of_le (S.equivFin ⟨C, hC⟩) ?_
  simp
