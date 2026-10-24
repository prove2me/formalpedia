-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.standardSimplex_sublevel_volume_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T07:09:26.401666+00:00
-- url     : https://prove2.me/submissions/dab17588-e679-4ea8-ab3e-3cbd5742c215

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplex_volume_factorial
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem solution (m : Nat) :
    (MeasureTheory.volume {x : Fin (m + 1) → Real | (∀ i : Fin (m + 1), 0 ≤ x i) ∧
      ∑ i : Fin (m + 1), x i ≤ 1}).toReal =
    (MeasureTheory.volume {x : Fin m → Real | (∀ i : Fin m, 0 ≤ x i) ∧
      ∑ i : Fin m, x i ≤ 1}).toReal / (m + 1 : Real) := by
  rw [standardSimplex_volume_factorial (m + 1), standardSimplex_volume_factorial m]
  rw [Nat.factorial_succ]
  have hfact : (Nat.factorial m : Real) ≠ 0 := by positivity
  have hsucc : (m + 1 : Real) ≠ 0 := by positivity
  push_cast
  field_simp
  <;> ring