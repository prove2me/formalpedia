-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.standardSimplex_region_volume_slicing
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T15:28:40.882594+00:00
-- url     : https://prove2.me/submissions/63d2548a-1924-486b-b089-53095f356f43

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplex_region_volume_fubini
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplex_region_interval_support
open scoped BigOperators

theorem solution (m : Nat) (H : Real) (hH : 0 < H) :
    (MeasureTheory.volume {x : Fin (m + 1) → Real | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ H}).toReal =
      ∫ t in (0 : Real)..H,
        (MeasureTheory.volume {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ H - t}).toReal := by
  rw [OAI.PiExponent.DeterminantContradiction.standardSimplex_region_volume_fubini]
  exact OAI.PiExponent.DeterminantContradiction.standardSimplex_region_interval_support m H hH