-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_factorial_aux
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T14:33:10.686911+00:00
-- url     : https://prove2.me/submissions/741e54cb-c46f-4489-990b-793c052750bb

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitSimplexVolume_factorial_aux_base
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitSimplexVolume_factorial_aux_step

theorem solution (n : Nat) :
    MeasureTheory.volume
      {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧
        (Finset.univ.sum fun i : Fin n => x i) ≤ 1} =
      ENNReal.ofReal (1 / (Nat.factorial n : Real)) := by
  induction n with
  | zero => exact OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_factorial_aux_base
  | succ n ih =>
      exact OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_factorial_aux_step n ih