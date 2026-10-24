-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.standardSimplex_measurable_subset_box
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T15:20:24.591637+00:00
-- url     : https://prove2.me/submissions/c40ffbbb-8696-475b-8f78-d86cc01bacca

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem solution (m : Nat) (A : Real) (hA : 0 ≤ A) :
    MeasurableSet {x : Fin (m + 1) → Real | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin (m + 1), x i ≤ A} ∧
      {x : Fin (m + 1) → Real | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin (m + 1), x i ≤ A} ⊆
        {x | ∀ i, x i ∈ Set.Icc (0 : Real) A} := by
  have hcoord_closed :
      IsClosed {x : Fin (m + 1) → Real | ∀ i, 0 ≤ x i} := by
    have heq :
        {x : Fin (m + 1) → Real | ∀ i, 0 ≤ x i} =
          ⋂ i : Fin (m + 1), {x | x i ∈ Set.Ici (0 : Real)} := by
      ext x
      simp
    rw [heq]
    exact isClosed_iInter fun i =>
      (isClosed_Ici : IsClosed (Set.Ici (0 : Real))).preimage (continuous_apply i)
  have hsum_cont :
      Continuous (fun x : Fin (m + 1) → Real => ∑ i : Fin (m + 1), x i) := by
    exact continuous_finset_sum Finset.univ (fun i hi => continuous_apply i)
  have hsum_closed :
      IsClosed {x : Fin (m + 1) → Real | ∑ i : Fin (m + 1), x i ≤ A} := by
    exact isClosed_Iic.preimage hsum_cont
  have hsimplex_closed :
      IsClosed
        {x : Fin (m + 1) → Real |
          (∀ i, 0 ≤ x i) ∧ ∑ i : Fin (m + 1), x i ≤ A} := by
    have heq :
        {x : Fin (m + 1) → Real |
            (∀ i, 0 ≤ x i) ∧ ∑ i : Fin (m + 1), x i ≤ A} =
          {x | ∀ i, 0 ≤ x i} ∩ {x | ∑ i : Fin (m + 1), x i ≤ A} := by
      ext x
      rfl
    rw [heq]
    exact hcoord_closed.inter hsum_closed
  constructor
  · exact hsimplex_closed.measurableSet
  · intro x hx i
    constructor
    · exact hx.1 i
    · calc
        x i ≤ ∑ j : Fin (m + 1), x j :=
          Finset.single_le_sum (fun j hj => hx.1 j) (Finset.mem_univ i)
        _ ≤ A := hx.2