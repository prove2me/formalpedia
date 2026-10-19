-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.unit_simplex_measurable
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T13:17:20.481627+00:00
-- url     : https://prove2.me/submissions/9dc6fd23-7f30-4364-a385-ff6e69437ad0

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open scoped BigOperators Topology

theorem solution (n : Nat) :
    MeasurableSet
      ({x : Fin n -> Real | (forall i, (0 : Real) <= x i) /\
        (Finset.univ.sum fun i => x i) <= (1 : Real)} : Set (Fin n -> Real)) := by
  have hsum : Continuous (fun x : Fin n -> Real => Finset.univ.sum fun i => x i) := by
    fun_prop
  have hclosed : IsClosed
      (Set.inter (Set.iInter fun i : Fin n => {x : Fin n -> Real | (0 : Real) <= x i})
        {x : Fin n -> Real | (Finset.univ.sum fun i => x i) <= (1 : Real)}) := by
    refine (isClosed_iInter fun i => ?_).inter (isClosed_le hsum continuous_const)
    exact isClosed_le continuous_const (continuous_apply i)
  have hset :
      ({x : Fin n -> Real | (forall i, (0 : Real) <= x i) /\
        (Finset.univ.sum fun i => x i) <= (1 : Real)} : Set (Fin n -> Real)) =
        Set.inter (Set.iInter fun i : Fin n => {x : Fin n -> Real | (0 : Real) <= x i})
          {x : Fin n -> Real | (Finset.univ.sum fun i => x i) <= (1 : Real)} := by
    ext x
    constructor
    · intro hx
      exact ⟨Set.mem_iInter.mpr hx.1, hx.2⟩
    · intro hx
      exact ⟨Set.mem_iInter.mp hx.1, hx.2⟩
  rw [hset]
  exact hclosed.measurableSet