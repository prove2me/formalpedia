-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplexVolumeScaled
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T13:34:43.2579+00:00
-- url     : https://prove2.me/submissions/291bcec9-aa7e-4c41-8b27-85d76d8dbb2b

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolumeScaled_zero
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolumeScaled_succ_of_lower
open scoped BigOperators

theorem solution (n : Nat) (r : Real) (hr : 0 ≤ r) :
    MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ r} =
      ENNReal.ofReal (r ^ n / (Nat.factorial n : Real)) := by
  revert r hr
  induction n with
  | zero =>
      intro r hr
      exact OAI.PiExponent.DeterminantContradiction.simplexVolumeScaled_zero r hr
  | succ n ih =>
      intro r hr
      exact OAI.PiExponent.DeterminantContradiction.simplexVolumeScaled_succ_of_lower
        n r hr (fun s hs => ih s hs)