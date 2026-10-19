-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_slice_volume
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T21:14:40.77929+00:00
-- url     : https://prove2.me/submissions/a92d2f30-c69d-490a-b27b-ab4a3bdd0f23

import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_slice_volume_unit
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_slice_volume_scale

open scoped BigOperators

theorem solution (m : ℕ) (a : ℝ) (ha : 0 ≤ a) :
    (MeasureTheory.volume
      {x : Fin m → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, x i ≤ a}).toReal =
      (a ^ m) / (Nat.factorial m : ℝ) := by
  rw [OAI.PiExponent.DeterminantContradiction.simplex_slice_volume_scale m a ha,
    OAI.PiExponent.DeterminantContradiction.simplex_slice_volume_unit m]
  ring