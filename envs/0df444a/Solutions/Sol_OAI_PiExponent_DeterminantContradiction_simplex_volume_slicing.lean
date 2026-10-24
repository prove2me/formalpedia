-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_volume_slicing
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T07:31:42.226168+00:00
-- url     : https://prove2.me/submissions/d614d7cc-3067-4ff2-91e3-3e1149a75262

import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_coordinate_volume_formula
import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem solution (n : Nat) :
    (MeasureTheory.volume {x : Fin (n + 1) → Real | (∀ i : Fin (n + 1), 0 ≤ x i) ∧
      ∑ i : Fin (n + 1), x i ≤ 1}).toReal =
    ((MeasureTheory.volume {x : Fin n → Real | (∀ i : Fin n, 0 ≤ x i) ∧
      ∑ i : Fin n, x i ≤ 1}).toReal) / ((n + 1 : Nat) : Real) := by
  rw [OAI.PiExponent.DeterminantContradiction.simplex_coordinate_volume_formula (n + 1),
    OAI.PiExponent.DeterminantContradiction.simplex_coordinate_volume_formula n]
  simp only [Nat.factorial_succ]
  push_cast
  field_simp
  <;> ring