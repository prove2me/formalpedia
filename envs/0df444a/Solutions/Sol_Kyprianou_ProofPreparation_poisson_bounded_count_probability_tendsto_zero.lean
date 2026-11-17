-- Prove2me | solution 1 for Kyprianou.ProofPreparation.poisson_bounded_count_probability_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:48:04.683404+00:00
-- url     : https://prove2.me/submissions/3f16e4b5-d8ea-4130-9f46-8957e78c0ca6

import Mathlib
import Theorems.Thm_Kyprianou_ProofPreparation_poisson_singleton_probability_tendsto_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal Nat Topology
open Kyprianou Kyprianou.ProofPreparation
set_option autoImplicit false
noncomputable section

theorem solution
    (rate : ℕ → ℝ≥0)
    (hrate : Tendsto (fun n => (rate n : ℝ)) atTop atTop)
    (k : ℕ) :
    Tendsto (fun n => (poissonMeasure (rate n)) (Set.Iic k))
      atTop (𝓝 0) := by
  have hI : (Set.Iic k : Set ℕ) =
      ⋃ j ∈ Finset.range (k + 1), ({j} : Set ℕ) := by
    ext j
    simp only [Set.mem_Iic, Set.mem_iUnion, Set.mem_singleton_iff,
      Finset.mem_range, exists_prop, Nat.lt_succ_iff]
    constructor
    · intro hj
      exact ⟨j, hj, rfl⟩
    · rintro ⟨j', hj', heq⟩
      rwa [← heq] at hj'
  have hpair : ((↑(Finset.range (k + 1)) : Set ℕ)).PairwiseDisjoint
      (fun j : ℕ => ({j} : Set ℕ)) := by
    intro i hi j hj hij
    exact Set.disjoint_singleton.mpr hij
  have heq (n : ℕ) :
      (poissonMeasure (rate n)) (Set.Iic k) =
        ∑ j ∈ Finset.range (k + 1), (poissonMeasure (rate n)) {j} := by
    rw [hI]
    exact measure_biUnion_finset hpair
      (fun j hj => MeasurableSet.singleton j)
  have hsum : Tendsto
      (fun n => ∑ j ∈ Finset.range (k + 1),
        (poissonMeasure (rate n)) {j}) atTop
        (𝓝 (∑ j ∈ Finset.range (k + 1), (0 : ENNReal))) :=
    tendsto_finset_sum (Finset.range (k + 1))
      (fun j hj => poisson_singleton_probability_tendsto_zero rate hrate j)
  simp only [Finset.sum_const_zero] at hsum
  simpa only [heq] using hsum
