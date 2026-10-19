-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.standard_simplex_region_volume
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T03:14:35.167177+00:00
-- url     : https://prove2.me/submissions/4dd227b9-f71f-45c4-8779-3b8b50163572

import Mathlib
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standard_simplex_unit_volume
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standard_simplex_region_volume_scale

open scoped BigOperators Topology

theorem solution
    (m : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    ENNReal.toReal (MeasureTheory.volume
      {x : Fin m → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, x i ≤ T}) =
      T ^ m / (Nat.factorial m : ℝ) := by
  rw [OAI.PiExponent.DeterminantContradiction.standard_simplex_region_volume_scale
    m T hT]
  rw [OAI.PiExponent.DeterminantContradiction.standard_simplex_unit_volume]
  ring