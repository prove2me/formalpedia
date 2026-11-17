-- Prove2me | solution 1 for LevyStochCalc.Poisson.indep_iSup_comap_of_disjoint_families_ch02
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T00:09:28.851599+00:00
-- url     : https://prove2.me/submissions/b4767b73-b958-44f3-a59a-099237887391

import Mathlib
import Definitions.Def_Kyprianou_Ch02_PartitionAtomV2
import Theorems.Thm_LevyStochCalc_Poisson_eq_biUnion_partitionAtom_ch02
import Theorems.Thm_LevyStochCalc_Poisson_partitionAtom_subset_iUnion_ch02
import Theorems.Thm_LevyStochCalc_Poisson_pairwise_disjoint_partitionAtom_ch02
import Theorems.Thm_LevyStochCalc_Poisson_measurableSet_partitionAtom_ch02
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson
set_option autoImplicit false
universe u v
/-- The mass of each measurable cell is the sum of masses of its
    disjoint partition atoms selected by the cell index. -/
private theorem measure_eq_sum_partitionAtom_ch02
    {𝓨 : Type u} [MeasurableSpace 𝓨] {n : ℕ}
    {C : Fin n → Set 𝓨}
    (μ : Measure 𝓨) (hC : ∀ i, MeasurableSet (C i))
    (i : Fin n) :
    μ (C i) = ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => i ∈ S),
      μ (partitionAtom C S) := by
  rw [eq_biUnion_partitionAtom_ch02 (C := C) i]
  exact measure_biUnion_finset
    (fun S _ T _ hST => pairwise_disjoint_partitionAtom_ch02 (by simpa using hST))
    (fun S _ => measurableSet_partitionAtom_ch02 hC S)

theorem solution
    {Ω : Type u} [MeasurableSpace Ω]
  {𝓨 : Type v} [MeasurableSpace 𝓨]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {N : Ω → Measure 𝓨}
    (hN_meas : ∀ {B : Set 𝓨}, MeasurableSet B → Measurable (fun ω => N ω B))
    (hN_indep : ∀ {ι : Type} [Countable ι] (B : ι → Set 𝓨), (∀ i, MeasurableSet (B i)) →
      Pairwise (fun i j => Disjoint (B i) (B j)) → iIndepFun (fun i ω => N ω (B i)) P)
    {n p : ℕ} (C : Fin n → Set 𝓨) (D : Fin p → Set 𝓨)
    (hC : ∀ i, MeasurableSet (C i)) (hD : ∀ j, MeasurableSet (D j))
    (hCD : ∀ i j, Disjoint (C i) (D j)) :
    Indep (⨆ i, MeasurableSpace.comap (fun ω => N ω (C i)) inferInstance)
      (⨆ j, MeasurableSpace.comap (fun ω => N ω (D j)) inferInstance) P := by
  classical
  set F : Finset (Fin n) ⊕ Finset (Fin p) → Set 𝓨 :=
    Sum.elim (partitionAtom C) (partitionAtom D) with hFdef
  have hF_meas : ∀ o, MeasurableSet (F o) := by
    rintro (S | T)
    · exact measurableSet_partitionAtom_ch02 hC S
    · exact measurableSet_partitionAtom_ch02 hD T
  have hCD' : Disjoint (⋃ i, C i) (⋃ j, D j) :=
    Set.disjoint_iUnion_left.2 fun i => Set.disjoint_iUnion_right.2 fun j => hCD i j
  have hF_disj : Pairwise fun o o' => Disjoint (F o) (F o') := by
    rintro (S | T) (S' | T') h
    · exact pairwise_disjoint_partitionAtom_ch02 (by simpa using h)
    · exact hCD'.mono (partitionAtom_subset_iUnion_ch02 S) (partitionAtom_subset_iUnion_ch02 T')
    · exact (hCD'.mono (partitionAtom_subset_iUnion_ch02 S') (partitionAtom_subset_iUnion_ch02 T)).symm
    · exact pairwise_disjoint_partitionAtom_ch02 (by simpa using h)
  have hind : iIndepFun (fun o ω => N ω (F o)) P := hN_indep F hF_meas hF_disj
  have hsplit := indep_iSup_of_disjoint (fun o => (hN_meas (hF_meas o)).comap_le) hind.iIndep
    (S := Set.range (Sum.inl : Finset (Fin n) → Finset (Fin n) ⊕ Finset (Fin p)))
    (T := Set.range (Sum.inr : Finset (Fin p) → Finset (Fin n) ⊕ Finset (Fin p)))
    (by simp [Set.disjoint_left])
  refine indep_of_indep_of_le_left (indep_of_indep_of_le_right hsplit ?_) ?_
  · refine iSup_le fun j => ?_
    have hcount : (fun ω => N ω (D j))
        = fun ω => ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin p) => j ∈ T),
            N ω (partitionAtom D T) :=
      funext fun ω => measure_eq_sum_partitionAtom_ch02 (N ω) hD j
    rw [hcount]
    refine Measurable.comap_le ?_
    letI : MeasurableSpace Ω :=
      ⨆ o ∈ Set.range (Sum.inr : Finset (Fin p) → Finset (Fin n) ⊕ Finset (Fin p)),
        MeasurableSpace.comap (fun ω => N ω (F o)) inferInstance
    exact Finset.measurable_sum _ fun T _ =>
      Measurable.of_comap_le (le_iSup₂_of_le (Sum.inr T) ⟨T, rfl⟩ le_rfl)
  · refine iSup_le fun i => ?_
    have hcount : (fun ω => N ω (C i))
        = fun ω => ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => i ∈ S),
            N ω (partitionAtom C S) :=
      funext fun ω => measure_eq_sum_partitionAtom_ch02 (N ω) hC i
    rw [hcount]
    refine Measurable.comap_le ?_
    letI : MeasurableSpace Ω :=
      ⨆ o ∈ Set.range (Sum.inl : Finset (Fin n) → Finset (Fin n) ⊕ Finset (Fin p)),
        MeasurableSpace.comap (fun ω => N ω (F o)) inferInstance
    exact Finset.measurable_sum _ fun S _ =>
      Measurable.of_comap_le (le_iSup₂_of_le (Sum.inl S) ⟨S, rfl⟩ le_rfl)
