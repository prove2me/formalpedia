-- Prove2me | solution 1 for Kyprianou.Ch02.iIndepFiniteFromOutsideJoinV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T12:31:45.681804+00:00
-- url     : https://prove2.me/submissions/92f10687-6307-46b3-808a-80868cf9b637

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ)
    (m : Fin n → MeasurableSpace Ω)
    (hm : ∀ i, m i ≤ (inferInstance : MeasurableSpace Ω))
    (hInd : ∀ (i : Fin n) (s : Finset (Fin n)), i ∉ s →
      ProbabilityTheory.Indep (m i) (⨆ j ∈ s, m j) P) :
    ProbabilityTheory.iIndep m P := by
  classical
  apply (iIndep_iff m P).2
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro f hf
      simp
  | @insert i s hi ih =>
      intro f hf
      have hfi : MeasurableSet[m i] (f i) :=
        hf i (Finset.mem_insert_self _ _)
      have hfs : ∀ j, j ∈ s → MeasurableSet[m j] (f j) := by
        intro j hj
        exact hf j (Finset.mem_insert_of_mem hj)
      have hprev := ih hfs
      have hjoint : MeasurableSet[(⨆ j ∈ s, m j)]
          (⋂ j ∈ s, f j) := by
        apply MeasurableSet.iInter
        intro j
        apply MeasurableSet.iInter
        intro hj
        have hle : m j ≤ (⨆ k ∈ s, m k) :=
          le_iSup₂_of_le j hj le_rfl
        exact hle _ (hfs j hj)
      have hset : IndepSet (f i) (⋂ j ∈ s, f j) P :=
        (hInd i s hi).indepSet_of_measurableSet hfi hjoint
      rw [Finset.set_biInter_insert, Finset.prod_insert hi,
        hset.measure_inter_eq_mul, hprev]
