-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplexVolume_zero_v2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T15:02:38.196013+00:00
-- url     : https://prove2.me/submissions/847a6ff1-0fe5-4b96-a3af-2087ae96687b

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
open scoped BigOperators

theorem solution :
    MeasureTheory.volume
        {x : Fin 0 → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} =
      ENNReal.ofReal (1 / (Nat.factorial 0 : Real)) := by
  have hs :
      {x : Fin 0 → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} =
        Set.pi Set.univ (fun _ : Fin 0 => (Set.univ : Set Real)) := by
    ext x
    simp
  rw [hs, MeasureTheory.volume_pi_pi]
  simp