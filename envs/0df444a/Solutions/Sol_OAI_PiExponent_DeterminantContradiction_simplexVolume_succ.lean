-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplexVolume_succ
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T02:54:29.879029+00:00
-- url     : https://prove2.me/submissions/ed29599c-96f8-4a3e-9076-8917ef1e2c70

import Mathlib
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_eq_inv_factorial

open scoped BigOperators Topology

theorem solution (n : ℕ) :
    ENNReal.toReal (MeasureTheory.volume
      {x : Fin (n + 1) → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin (n + 1), x i ≤ (1 : ℝ)}) =
    ((n + 1 : ℕ) : ℝ)⁻¹ * ENNReal.toReal (MeasureTheory.volume
      {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin n, x i ≤ (1 : ℝ)}) := by
  rw [OAI.PiExponent.DeterminantContradiction.simplexVolume_eq_inv_factorial (n + 1)]
  rw [OAI.PiExponent.DeterminantContradiction.simplexVolume_eq_inv_factorial n]
  rw [Nat.factorial_succ, Nat.cast_mul]
  have hn : (↑(n + 1) : ℝ) ≠ 0 := by positivity
  have hf : (↑(Nat.factorial n) : ℝ) ≠ 0 := by positivity
  field_simp [hn, hf] <;> ring