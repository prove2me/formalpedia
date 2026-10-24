-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.standardSimplex_region_interval_support.fiber_zero_outside
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T20:06:09.520806+00:00
-- url     : https://prove2.me/submissions/f658a09d-6c9b-412f-b052-bf1424bdd7cf

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib
open scoped BigOperators

open MeasureTheory Filter Topology in

theorem solution (m : Nat) (H t : Real) (ht : t < 0 ∨ H < t) :
    (MeasureTheory.volume {x : Fin m → Real | 0 ≤ t ∧ (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ H - t}).toReal = 0 := by
  have : {x : Fin m → Real | 0 ≤ t ∧ (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ H - t} = ∅ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro h0 hx hs
    have : 0 ≤ ∑ i, x i := Finset.sum_nonneg (fun i _ => hx i)
    rcases ht with ht | ht <;> linarith
  simp [this]
