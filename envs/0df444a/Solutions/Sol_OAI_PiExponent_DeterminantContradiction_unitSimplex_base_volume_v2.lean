-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.unitSimplex_base_volume_v2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T20:06:13.918296+00:00
-- url     : https://prove2.me/submissions/279670b2-3eb8-4161-9e32-96c40d281a10

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitSimplexVolume_factorial_aux

open MeasureTheory

open MeasureTheory Filter Topology in

theorem solution (n : Nat) :
    MeasureTheory.volume
      {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧
        (Finset.univ.sum fun i : Fin n => x i) ≤ 1} =
    ENNReal.ofReal (1 / (n.factorial : Real)) := by
  exact OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_factorial_aux n
