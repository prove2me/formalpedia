-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_volume_zero_ENNReal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T19:39:02.789999+00:00
-- url     : https://prove2.me/submissions/98bb4f44-1484-4333-85f6-9a1378c36e6d

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitSimplexVolume_factorial_aux_base
open MeasureTheory

theorem solution :
    MeasureTheory.volume
      {x : Fin 0 → Real | (∀ i, 0 ≤ x i) ∧
        (Finset.univ.sum fun i : Fin 0 => x i) ≤ 1} =
      ENNReal.ofReal (1 / (Nat.factorial 0 : Real)) := by
  apply OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_factorial_aux_base <;> assumption
