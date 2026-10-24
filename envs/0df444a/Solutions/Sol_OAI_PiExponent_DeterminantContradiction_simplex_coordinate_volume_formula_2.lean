-- Prove2me | solution 2 for OAI.PiExponent.DeterminantContradiction.simplex_coordinate_volume_formula
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T07:45:36.84402+00:00
-- url     : https://prove2.me/submissions/7d1ec0f0-198c-480c-8b0b-da7f36d02fc9

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_coordinate_volume_zero
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_coordinate_volume_slice
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_coordinate_scaled_section_integral
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_coordinate_power_integral
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
      rw [OAI.PiExponent.DeterminantContradiction.simplex_coordinate_volume_slice,
        OAI.PiExponent.DeterminantContradiction.simplex_coordinate_scaled_section_integral,
        OAI.PiExponent.DeterminantContradiction.simplex_coordinate_power_integral,
        ih, Nat.factorial_succ]
      field_simp
      push_cast
      ring