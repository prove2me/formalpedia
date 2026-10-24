-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weightedSimplex_region_volume
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T15:11:05.143584+00:00
-- url     : https://prove2.me/submissions/82283b1c-9d26-4691-ad10-dd0208b3bf6b

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_volume_eq_unweighted_div_weights
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplex_region_volume
open scoped BigOperators

theorem solution {m : Nat} (w : Fin m → Real) (H : Real)
    (hw : ∀ i, 0 < w i) (hH : 0 < H) :
    (MeasureTheory.volume {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i, w i * x i ≤ H}).toReal =
      H ^ m / ((Nat.factorial m : Nat) : Real) / ∏ i : Fin m, w i := by
  rw [OAI.PiExponent.DeterminantContradiction.weightedSimplex_volume_eq_unweighted_div_weights
    w H hw hH]
  rw [OAI.PiExponent.DeterminantContradiction.standardSimplex_region_volume H hH]