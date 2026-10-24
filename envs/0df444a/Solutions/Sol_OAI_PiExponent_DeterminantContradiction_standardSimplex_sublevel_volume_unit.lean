-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.standardSimplex_sublevel_volume_unit
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T07:03:33.323813+00:00
-- url     : https://prove2.me/submissions/da987bb4-bc6e-4ad5-8250-901e4218c548

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplex_sublevel_volume_zero
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplex_sublevel_volume_recurrence
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem solution {m : Nat} :
    (MeasureTheory.volume {x : Fin m → Real | (∀ i : Fin m, 0 ≤ x i) ∧
      ∑ i : Fin m, x i ≤ 1}).toReal = 1 / (m.factorial : Real) := by
  induction m with
  | zero =>
      simpa using
        OAI.PiExponent.DeterminantContradiction.standardSimplex_sublevel_volume_zero
  | succ n ih =>
      rw [OAI.PiExponent.DeterminantContradiction.standardSimplex_sublevel_volume_recurrence n, ih]
      rw [Nat.factorial_succ]
      push_cast
      field_simp [Nat.factorial_ne_zero]