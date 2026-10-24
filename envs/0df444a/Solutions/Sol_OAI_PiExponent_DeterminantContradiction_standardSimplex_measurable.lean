-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.standardSimplex_measurable
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T13:24:27.370997+00:00
-- url     : https://prove2.me/submissions/a225f9af-a5f5-4719-9e23-89444d2ed5b6

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem solution (n : Nat) :
    MeasurableSet {y : Fin n → Real | (∀ i, 0 ≤ y i) ∧ (∑ i, y i) ≤ 1} := by
  have hcoord : IsClosed {y : Fin n → Real | ∀ i, 0 ≤ y i} := by
    convert isClosed_iInter (fun i : Fin n =>
      isClosed_le (continuous_const : Continuous fun _ : (Fin n → Real) => (0 : Real))
        (continuous_apply i)) using 1 <;> ext y <;> simp
  have hsum : IsClosed {y : Fin n → Real | (∑ i, y i) ≤ 1} := by
    have hcontinuous : Continuous (fun y : Fin n → Real => ∑ i, y i) := by
      apply continuous_finset_sum
      intro i hi
      exact continuous_apply i
    convert isClosed_le hcontinuous
      (continuous_const : Continuous fun _ : (Fin n → Real) => (1 : Real)) using 1 <;> ext y <;> simp
  have hsimplex : IsClosed
      {y : Fin n → Real | (∀ i, 0 ≤ y i) ∧ (∑ i, y i) ≤ 1} := by
    convert hcoord.inter hsum using 1 <;> ext y <;> simp
  exact hsimplex.measurableSet