-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_coordinate_volume_formula
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T07:39:01.251174+00:00
-- url     : https://prove2.me/submissions/ba03d2e2-5010-433a-a63b-37180f98dadc

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_coordinate_volume_zero
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_coordinate_volume_succ
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem solution (n : Nat) :
    (MeasureTheory.volume {x : Fin n → Real | (∀ i : Fin n, 0 ≤ x i) ∧
      ∑ i : Fin n, x i ≤ 1}).toReal = 1 / (Nat.factorial n : Real) := by
  induction n with
  | zero =>
      simpa using OAI.PiExponent.DeterminantContradiction.simplex_coordinate_volume_zero
  | succ n ih =>
      rw [OAI.PiExponent.DeterminantContradiction.simplex_coordinate_volume_succ n, ih,
        Nat.factorial_succ]
      field_simp
      push_cast
      ring