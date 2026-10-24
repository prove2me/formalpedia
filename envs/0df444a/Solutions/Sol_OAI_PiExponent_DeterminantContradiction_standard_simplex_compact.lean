-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.standard_simplex_compact
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T07:56:54.182641+00:00
-- url     : https://prove2.me/submissions/bea131fa-c43a-46ac-a76b-a28af413b9e2

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open Filter Topology
open scoped BigOperators

theorem solution {m : Nat} (A : Real) (hA : 0 < A) :
    IsCompact {y : Fin m → Real | (∀ i : Fin m, 0 ≤ y i) ∧ ∑ i : Fin m, y i ≤ A} := by
  apply Metric.isCompact_iff_isClosed_bounded.mpr
  constructor
  · change IsClosed
      ({y : Fin m → Real | ∀ i : Fin m, 0 ≤ y i} ∩
        {y : Fin m → Real | ∑ i : Fin m, y i ≤ A})
    have hcoord : IsClosed
        ({y : Fin m → Real | ∀ i : Fin m, 0 ≤ y i} : Set (Fin m → Real)) := by
      rw [Set.ofPred_forall]
      exact isClosed_iInter fun i =>
        (isClosed_Ici : IsClosed (Set.Ici (0 : Real))).preimage (continuous_apply i)
    have hsum : IsClosed
        ({y : Fin m → Real | ∑ i : Fin m, y i ≤ A} : Set (Fin m → Real)) := by
      exact isClosed_le (by fun_prop) continuous_const
    exact hcoord.inter hsum
  · rw [isBounded_iff_forall_norm_le]
    refine ⟨A, fun y hy => ?_⟩
    rcases hy with ⟨hy_nonneg, hy_sum⟩
    apply (pi_norm_le_iff_of_nonneg hA.le).2
    intro i
    have hi_sum : y i ≤ ∑ j : Fin m, y j :=
      Finset.single_le_sum (s := Finset.univ) (f := fun j : Fin m => y j)
        (fun j hj => hy_nonneg j) (Finset.mem_univ i)
    rw [Real.norm_eq_abs, abs_of_nonneg (hy_nonneg i)]
    exact hi_sum.trans hy_sum