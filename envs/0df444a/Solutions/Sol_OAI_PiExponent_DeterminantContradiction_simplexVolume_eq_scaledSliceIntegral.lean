-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplexVolume_eq_scaledSliceIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T02:25:50.290481+00:00
-- url     : https://prove2.me/submissions/b604be7b-968f-4cd9-a2f8-aed6f83b59f1

import Mathlib
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplexVolume_eq_factorial
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_scaledSliceIntegral_eq_inv

open scoped BigOperators Topology

theorem solution (n : ℕ) :
    ENNReal.toReal (MeasureTheory.volume
      {x : Fin (n + 1) → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin (n + 1), x i ≤ (1 : ℝ)}) =
    ENNReal.toReal (MeasureTheory.volume
      {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin n, x i ≤ (1 : ℝ)}) *
      ENNReal.toReal (∫⁻ t : ℝ,
        (if 0 ≤ t ∧ t ≤ 1 then ENNReal.ofReal (1 - t) ^ n else 0)
        ∂MeasureTheory.volume) := by
  rw [OAI.PiExponent.DeterminantContradiction.simplexVolume_eq_factorial (n + 1),
    OAI.PiExponent.DeterminantContradiction.simplexVolume_eq_factorial n,
    OAI.PiExponent.DeterminantContradiction.scaledSliceIntegral_eq_inv n,
    Nat.factorial_succ]
  push_cast
  have hn : (↑(n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hfact : (↑(Nat.factorial n : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hn, hfact] <;> ring