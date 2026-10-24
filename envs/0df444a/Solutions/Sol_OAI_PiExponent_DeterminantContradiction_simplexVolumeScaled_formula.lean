-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplexVolumeScaled_formula
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T13:57:46.207958+00:00
-- url     : https://prove2.me/submissions/20fc32a9-dc38-482c-b674-64b108b34e7a

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolumeScaled_scale
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_unit
open scoped BigOperators

theorem solution (n : Nat) (r : Real) (hr : 0 ≤ r) :
    MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ r} =
      ENNReal.ofReal (r ^ n / (Nat.factorial n : Real)) := by
  rw [OAI.PiExponent.DeterminantContradiction.simplexVolumeScaled_scale n r hr,
    OAI.PiExponent.DeterminantContradiction.simplexVolume_unit n]
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ r ^ n)]
  congr 1
  simp [div_eq_mul_inv]