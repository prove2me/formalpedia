-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_unit_volume_base
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T07:07:31.336651+00:00
-- url     : https://prove2.me/submissions/5dbfadd9-c160-4a36-9ba1-3e8a2cb51634

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.Nat.Factorial.Basic

open scoped BigOperators

theorem solution :
    (MeasureTheory.volume
      {x : Fin 0 → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin 0, x i ≤ 1}).toReal =
      (Nat.factorial 0 : ℝ)⁻¹ := by
  have hs :
      {x : Fin 0 → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin 0, x i ≤ 1} = Set.univ := by
    ext x
    simp
  rw [hs, MeasureTheory.Measure.volume_pi_eq_dirac (fun _ : Fin 0 => (0 : ℝ))]
  simp [Nat.factorial_zero]