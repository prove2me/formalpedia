-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.standardSimplex_region_interval_support.fiber_eq_inside
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T20:09:56.225882+00:00
-- url     : https://prove2.me/submissions/10b1769b-3a07-4df7-a2b7-ed7938f403b5

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib
open scoped BigOperators

open MeasureTheory Filter Topology in

theorem solution (m : Nat) (H t : Real) (ht0 : 0 < t) (htH : t < H) :
    (MeasureTheory.volume {x : Fin m → Real | 0 ≤ t ∧ (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ H - t}).toReal =
      (MeasureTheory.volume {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ H - t}).toReal := by
  simp [ht0.le]
