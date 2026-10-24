-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.standardSimplex_region_volume
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T15:15:20.707918+00:00
-- url     : https://prove2.me/submissions/370dfde7-8789-4af1-8efe-a14daaac188e

import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplex_region_volume_base
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplex_region_volume_step
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem solution {m : Nat} (H : Real) (hH : 0 < H) :
    (MeasureTheory.volume {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ H}).toReal =
      H ^ m / ((Nat.factorial m : Nat) : Real) := by
  have general : ∀ (m : Nat) (H : Real), 0 < H →
      (MeasureTheory.volume {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ H}).toReal =
        H ^ m / ((Nat.factorial m : Nat) : Real) := by
    intro m
    induction m with
    | zero =>
        intro H hH
        simpa using OAI.PiExponent.DeterminantContradiction.standardSimplex_region_volume_base H hH
    | succ m ih =>
        intro H hH
        exact OAI.PiExponent.DeterminantContradiction.standardSimplex_region_volume_step H hH ih
  exact general m H hH