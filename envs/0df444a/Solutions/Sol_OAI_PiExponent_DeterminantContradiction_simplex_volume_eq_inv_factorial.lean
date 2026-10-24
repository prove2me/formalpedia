-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_volume_eq_inv_factorial
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T07:28:57.382843+00:00
-- url     : https://prove2.me/submissions/9f31bbd2-5fdd-4fb7-8e92-ab2867f2c5c5

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_volume_zero_measure
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_volume_slicing
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem solution (n : Nat) :
    (MeasureTheory.volume {x : Fin n → Real | (∀ i : Fin n, 0 ≤ x i) ∧
      ∑ i : Fin n, x i ≤ 1}).toReal = 1 / (Nat.factorial n : Real) := by
  induction n with
  | zero =>
      simpa [Nat.factorial] using
        OAI.PiExponent.DeterminantContradiction.simplex_volume_zero_measure
  | succ n ih =>
      rw [OAI.PiExponent.DeterminantContradiction.simplex_volume_slicing n, ih,
        Nat.factorial_succ]
      push_cast
      have hn : (0 : Real) < (n + 1 : Real) := by positivity
      have hf : (0 : Real) < (Nat.factorial n : Real) := by positivity
      field_simp [ne_of_gt hn, ne_of_gt hf] <;> ring