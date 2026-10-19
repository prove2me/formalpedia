-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.volume_smul_image_fin_real
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T03:24:19.9015+00:00
-- url     : https://prove2.me/submissions/c5a479b0-79f4-4279-afdd-a832871d9351

import Mathlib
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_volume_smul_image_fin_real_of_ne_zero
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_volume_smul_image_fin_real_zero

open scoped BigOperators Topology

theorem solution
    (m : ℕ) (T : ℝ) (hT : 0 ≤ T) (s : Set (Fin m → ℝ)) :
    ENNReal.toReal (MeasureTheory.volume ((fun x : Fin m → ℝ => T • x) '' s)) =
      T ^ m * ENNReal.toReal (MeasureTheory.volume s) := by
  by_cases hT0 : T = 0
  · subst T
    exact OAI.PiExponent.DeterminantContradiction.volume_smul_image_fin_real_zero m s
  · exact OAI.PiExponent.DeterminantContradiction.volume_smul_image_fin_real_of_ne_zero
      m T hT hT0 s