-- Prove2me | solution 1 for LevyStochCalc.Poisson.indep_of_disjoint_region_of_indep
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T06:55:01.00046+00:00
-- url     : https://prove2.me/submissions/b61fdd6c-d1be-485b-a116-ab9185289b05

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

theorem AuxFam.region
    (hN_meas : ∀ {B : Set 𝓨}, MeasurableSet B → Measurable (fun ω => N ω B))
    (hN_indep : ∀ {ι : Type} [Countable ι] (B : ι → Set 𝓨), (∀ i, MeasurableSet (B i)) →
      Pairwise (fun i j => Disjoint (B i) (B j)) → iIndepFun (fun i ω => N ω (B i)) P)
    {p : ℕ} (D : Fin p → Set 𝓨) (hD : ∀ j, MeasurableSet (D j)) :
    Indep (⨆ C ∈ {C : Set 𝓨 | (∀ j, Disjoint C (D j)) ∧ MeasurableSet C},
        MeasurableSpace.comap (fun ω => N ω C) inferInstance)
      (⨆ j, MeasurableSpace.comap (fun ω => N ω (D j)) inferInstance) P := by
  classical
  let S := {C : Set 𝓨 // (∀ j, Disjoint C (D j)) ∧ MeasurableSet C}
  let mF : Finset S → MeasurableSpace Ω := fun F =>
    ⨆ C ∈ F, MeasurableSpace.comap (fun ω => N ω C.1) inferInstance
  have hcomap_le : ∀ {B : Set 𝓨}, MeasurableSet B →
      MeasurableSpace.comap (fun ω => N ω B) inferInstance ≤ ‹MeasurableSpace Ω› :=
    fun hB => (hN_meas hB).comap_le
  have hF : ∀ F : Finset S, Indep (mF F)
      (⨆ j, MeasurableSpace.comap (fun ω => N ω (D j)) inferInstance) P := by
    intro F
    let C' : Fin F.card → Set 𝓨 := fun i => (F.equivFin.symm i).1.1
    have h := AuxFam.fam (P := P) hN_meas hN_indep C' D
      (fun i => (F.equivFin.symm i).1.2.2) hD (fun i j => (F.equivFin.symm i).1.2.1 j)
    refine indep_of_indep_of_le_left h (iSup₂_le fun C hC => ?_)
    have e : C' (F.equivFin ⟨C, hC⟩) = C.1 := by simp [C']
    exact le_iSup_of_le (F.equivFin ⟨C, hC⟩) (by rw [e])
  have hdir : Directed (· ≤ ·) mF := by
    refine Monotone.directed_le fun F G hFG => ?_
    exact iSup₂_le fun C hC => le_iSup₂_of_le C (hFG hC) le_rfl
  have h := indep_iSup_of_directed_le hF
    (fun F => iSup₂_le fun C _ => hcomap_le C.2.2)
    (iSup_le fun j => hcomap_le (hD j)) hdir
  refine indep_of_indep_of_le_left h (iSup₂_le fun C hC => ?_)
  exact le_iSup_of_le {⟨C, hC⟩} (le_iSup₂_of_le (f := fun (c : S) (_ : c ∈ ({⟨C, hC⟩} : Finset S)) =>
    MeasurableSpace.comap (fun ω => N ω c.1) inferInstance) ⟨C, hC⟩
    (Finset.mem_singleton_self _) le_rfl)

theorem _root_.solution
    (hN_meas : ∀ {B : Set 𝓨}, MeasurableSet B → Measurable (fun ω => N ω B))
    (hN_indep : ∀ {ι : Type} [Countable ι] (B : ι → Set 𝓨), (∀ i, MeasurableSet (B i)) →
      Pairwise (fun i j => Disjoint (B i) (B j)) → iIndepFun (fun i ω => N ω (B i)) P)
    {D : Set 𝓨} (hD : MeasurableSet D) :
    Indep (⨆ C ∈ {C : Set 𝓨 | Disjoint C D ∧ MeasurableSet C},
        MeasurableSpace.comap (fun ω => N ω C) inferInstance)
      (MeasurableSpace.comap (fun ω => N ω D) inferInstance) P := by
  have h := AuxFam.region (P := P) hN_meas hN_indep (fun _ : Fin 1 => D) (fun _ => hD)
  rw [iSup_const] at h
  have e : {C : Set 𝓨 | (∀ _ : Fin 1, Disjoint C D) ∧ MeasurableSet C}
      = {C : Set 𝓨 | Disjoint C D ∧ MeasurableSet C} := by
    ext C; simp
  rwa [e] at h

end LevyStochCalc.Poisson
