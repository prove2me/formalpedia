-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_measurable
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T13:07:13.696255+00:00
-- url     : https://prove2.me/submissions/bd98a202-0fca-400a-b1d4-1a4f76b02dce

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem solution (m : Nat) (T : Real) :
    MeasurableSet {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) < T} := by
  have hcoords :
      MeasurableSet {x : Fin m → Real | ∀ i : Fin m, 0 ≤ x i} := by
    rw [Set.setOf_forall]
    exact MeasurableSet.iInter fun i => by
      have hEval : Continuous (fun x : Fin m → Real => x i) := continuous_apply i
      exact measurableSet_Ici.preimage hEval.measurable
  have hsum :
      MeasurableSet {x : Fin m → Real | (∑ i : Fin m, x i) < T} := by
    have hcont : Continuous (fun x : Fin m → Real => ∑ i : Fin m, x i) := by
      exact continuous_finset_sum Finset.univ (fun i hi => continuous_apply i)
    exact measurableSet_Iio.preimage hcont.measurable
  have hset :
      {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) < T} =
        {x : Fin m → Real | ∀ i : Fin m, 0 ≤ x i} ∩
          {x : Fin m → Real | (∑ i : Fin m, x i) < T} := by
    ext x
    simp
  rw [hset]
  exact hcoords.inter hsum