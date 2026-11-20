-- Prove2me | solution 1 for LevyStochCalc.Poisson.indep_iSup_comap_of_disjoint_of_indep
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T06:53:50.808346+00:00
-- url     : https://prove2.me/submissions/d3f3314c-070a-41be-a7cb-2dac2d8adc18

import Definitions.Def_LevyStochCalc_Poisson_RegionPartition_F000
import Definitions.Def_LevyStochCalc_Probability_IndepJoin_F000

open MeasureTheory ProbabilityTheory

namespace LevyStochCalc.Poisson

variable {Ω : Type*} [MeasurableSpace Ω] {𝓨 : Type*} [MeasurableSpace 𝓨]
  {P : Measure Ω} [IsProbabilityMeasure P] {N : Ω → Measure 𝓨}

omit [IsProbabilityMeasure P] in
theorem AuxFam.fam
    (hN_meas : ∀ {B : Set 𝓨}, MeasurableSet B → Measurable (fun ω => N ω B))
    (hN_indep : ∀ {ι : Type} [Countable ι] (B : ι → Set 𝓨), (∀ i, MeasurableSet (B i)) →
      Pairwise (fun i j => Disjoint (B i) (B j)) → iIndepFun (fun i ω => N ω (B i)) P)
    {n p : ℕ} (C : Fin n → Set 𝓨) (D : Fin p → Set 𝓨)
    (hC : ∀ i, MeasurableSet (C i)) (hD : ∀ j, MeasurableSet (D j))
    (hCD : ∀ i j, Disjoint (C i) (D j)) :
    Indep (⨆ i, MeasurableSpace.comap (fun ω => N ω (C i)) inferInstance)
      (⨆ j, MeasurableSpace.comap (fun ω => N ω (D j)) inferInstance) P := by
  classical
  let B : Finset (Fin n) ⊕ Finset (Fin p) → Set 𝓨 :=
    Sum.elim (partitionAtom C) (partitionAtom D)
  have hBm : ∀ k, MeasurableSet (B k) := by
    rintro (S | T)
    · exact measurableSet_partitionAtom hC S
    · exact measurableSet_partitionAtom hD T
  have hUD : Disjoint (⋃ i, C i) (⋃ j, D j) :=
    Set.disjoint_iUnion_left.2 fun i => Set.disjoint_iUnion_right.2 fun j => hCD i j
  have hBd : Pairwise (fun k l => Disjoint (B k) (B l)) := by
    rintro (S | T) (S' | T') h
    · exact pairwise_disjoint_partitionAtom (C := C) (fun e => h (by rw [e]))
    · exact hUD.mono (partitionAtom_subset_iUnion S) (partitionAtom_subset_iUnion T')
    · exact hUD.symm.mono (partitionAtom_subset_iUnion T) (partitionAtom_subset_iUnion S')
    · exact pairwise_disjoint_partitionAtom (C := D) (fun e => h (by rw [e]))
  have hI := hN_indep B hBm hBd
  let m : Finset (Fin n) ⊕ Finset (Fin p) → MeasurableSpace Ω :=
    fun k => MeasurableSpace.comap (fun ω => N ω (B k)) inferInstance
  have hle : ∀ k, m k ≤ ‹MeasurableSpace Ω› := fun k => (hN_meas (hBm k)).comap_le
  have hST : Disjoint (Set.range (Sum.inl : Finset (Fin n) → _))
      (Set.range (Sum.inr : Finset (Fin p) → _)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨S, rfl⟩ ⟨T, hT⟩
    cases hT
  have h := indep_iSup_of_disjoint hle hI hST
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left h ?_) ?_
  · refine iSup_le fun i => ?_
    have hmeas : Measurable[⨆ k ∈ Set.range (Sum.inl : Finset (Fin n) → _), m k]
        (fun ω => N ω (C i)) := by
      have e : (fun ω => N ω (C i)) = fun ω =>
          ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => i ∈ S), N ω (partitionAtom C S) :=
        funext fun ω => measure_eq_sum_partitionAtom (N ω) hC i
      rw [e]
      refine Finset.measurable_sum _ fun S _ => ?_
      refine Measurable.mono (ma := m (Sum.inl S)) ?_ ?_ le_rfl
      · exact comap_measurable _
      · exact le_iSup₂ (f := fun k (_ : k ∈ Set.range Sum.inl) => m k) (Sum.inl S) ⟨S, rfl⟩
    exact hmeas.comap_le
  · refine iSup_le fun j => ?_
    have hmeas : Measurable[⨆ k ∈ Set.range (Sum.inr : Finset (Fin p) → _), m k]
        (fun ω => N ω (D j)) := by
      have e : (fun ω => N ω (D j)) = fun ω =>
          ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin p) => j ∈ T), N ω (partitionAtom D T) :=
        funext fun ω => measure_eq_sum_partitionAtom (N ω) hD j
      rw [e]
      refine Finset.measurable_sum _ fun T _ => ?_
      refine Measurable.mono (ma := m (Sum.inr T)) ?_ ?_ le_rfl
      · exact comap_measurable _
      · exact le_iSup₂ (f := fun k (_ : k ∈ Set.range Sum.inr) => m k) (Sum.inr T) ⟨T, rfl⟩
    exact hmeas.comap_le

omit [IsProbabilityMeasure P] in
theorem _root_.solution
    (hN_meas : ∀ {B : Set 𝓨}, MeasurableSet B → Measurable (fun ω => N ω B))
    (hN_indep : ∀ {ι : Type} [Countable ι] (B : ι → Set 𝓨), (∀ i, MeasurableSet (B i)) →
      Pairwise (fun i j => Disjoint (B i) (B j)) → iIndepFun (fun i ω => N ω (B i)) P)
    {n : ℕ} {D : Set 𝓨} (hD : MeasurableSet D) (C : Fin n → Set 𝓨)
    (hC : ∀ i, MeasurableSet (C i)) (hCD : ∀ i, Disjoint (C i) D) :
    Indep (⨆ i, MeasurableSpace.comap (fun ω => N ω (C i)) inferInstance)
      (MeasurableSpace.comap (fun ω => N ω D) inferInstance) P := by
  have h := AuxFam.fam hN_meas hN_indep C (fun _ : Fin 1 => D) hC (fun _ => hD)
    (fun i _ => hCD i)
  rwa [iSup_const] at h

end LevyStochCalc.Poisson
