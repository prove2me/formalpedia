-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_coordinate_volume_succ
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T07:41:26.074358+00:00
-- url     : https://prove2.me/submissions/07844dbe-52d4-4e72-937e-82bc2811d13e

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_coordinate_volume_formula
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem solution (n : Nat) :
    (MeasureTheory.volume {x : Fin (n + 1) → Real | (∀ i : Fin (n + 1), 0 ≤ x i) ∧
      ∑ i : Fin (n + 1), x i ≤ 1}).toReal =
      (MeasureTheory.volume {x : Fin n → Real | (∀ i : Fin n, 0 ≤ x i) ∧
        ∑ i : Fin n, x i ≤ 1}).toReal / (n + 1 : Real) := by
  rw [OAI.PiExponent.DeterminantContradiction.simplex_coordinate_volume_formula,
    OAI.PiExponent.DeterminantContradiction.simplex_coordinate_volume_formula]
  rw [Nat.factorial_succ]
  push_cast
  have hfac : (Nat.factorial n : Real) ≠ 0 := by positivity
  have hnplus : (n + 1 : Real) ≠ 0 := by positivity
  field_simp [hfac, hnplus]
  <;> ring