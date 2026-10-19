-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplexVolume_eq_inv_factorial
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T03:02:25.516731+00:00
-- url     : https://prove2.me/submissions/24c66f9f-46f6-4ad7-8653-585a9eef2002

import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_base_case
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_successor_recurrence

open scoped BigOperators Topology

theorem solution (n : ℕ) :
    ENNReal.toReal (MeasureTheory.volume
      {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin n, x i ≤ (1 : ℝ)}) =
    ((Nat.factorial n : ℕ) : ℝ)⁻¹ := by
  induction n with
  | zero => exact OAI.PiExponent.DeterminantContradiction.simplexVolume_base_case
  | succ n ih =>
      rw [OAI.PiExponent.DeterminantContradiction.simplexVolume_successor_recurrence, ih,
        Nat.factorial_succ]
      push_cast
      have hn : (n + 1 : ℝ) ≠ 0 := by positivity
      field_simp [hn]