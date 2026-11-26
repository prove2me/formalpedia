-- Prove2me | solution 1 for ManyServerQED.Scheduling.independent_disjoint_groups_of_primitive_fields
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T02:49:41.385165+00:00
-- url     : https://prove2.me/submissions/52a90227-909a-4b41-a709-7182e9c2e992

import Mathlib

open Set MeasureTheory ProbabilityTheory

theorem solution {Ω ι κ : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (m : ι → MeasurableSpace Ω)
    (hLe : ∀ j, m j ≤ mΩ) (hInd : iIndep m P)
    (D : κ → Set ι) (hD : Pairwise (fun i j => Disjoint (D i) (D j))) :
    iIndep (fun i => ⨆ j ∈ D i, m j) P := by
  classical
  apply (iIndep_iff _ _).2
  intro S A hA
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
      let U := ⋃ j ∈ S, D j
      have hd : Disjoint (D i) U := by
        apply Set.disjoint_left.2
        intro a hai haU
        simp only [U, mem_iUnion] at haU
        obtain ⟨j,hj,haj⟩ := haU
        exact Set.disjoint_left.1 (hD (show i ≠ j from fun he => hi (he ▸ hj))) hai haj
      have h := indep_iSup_of_disjoint hLe hInd hd
      have hM : MeasurableSet[⨆ j ∈ U, m j] (⋂ j ∈ S, A j) := by
        apply MeasurableSet.biInter S.countable_toSet
        intro j hj
        have hsub : (⨆ a ∈ D j, m a) ≤ ⨆ a ∈ U, m a := by
          refine iSup₂_le fun a ha => le_iSup₂_of_le a ?_ le_rfl
          simp only [U, mem_iUnion]
          exact ⟨j,hj,ha⟩
        exact hsub _ (hA j (Finset.mem_insert_of_mem hj))
      have hMb := hA i (Finset.mem_insert_self i S)
      have he : (⋂ j ∈ insert i S, A j) = A i ∩ (⋂ j ∈ S, A j) := by
        ext ω; simp
      rw [he, (Indep_iff _ _ _).1 h _ _ hMb hM, Finset.prod_insert hi]
      rw [ih (fun j hj => hA j (Finset.mem_insert_of_mem hj))]
