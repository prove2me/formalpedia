-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.standardSimplex_volume_for_explicit_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T15:08:54.13582+00:00
-- url     : https://prove2.me/submissions/8bb6ce40-b8db-45e1-8703-dbe8befeace9

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplex_explicitBounds_volume_zero
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplex_explicitBounds_volume_succ_slice
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplex_explicitBounds_power_integral
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem solution {m : Nat} (A : Real) (hA : 0 ≤ A) :
    (MeasureTheory.volume {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, x i ≤ A}).toReal =
      A ^ m / ((Nat.factorial m : Nat) : Real) := by
  induction m generalizing A hA with
  | zero =>
      simpa using
        OAI.PiExponent.DeterminantContradiction.standardSimplex_explicitBounds_volume_zero A hA
  | succ m ih =>
      calc
        (MeasureTheory.volume {x : Fin (m + 1) → Real | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin (m + 1), x i ≤ A}).toReal =
            (∫ t in Set.Icc (0 : Real) A,
              (MeasureTheory.volume {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, x i ≤ A - t}).toReal) :=
          OAI.PiExponent.DeterminantContradiction.standardSimplex_explicitBounds_volume_succ_slice m A hA
        _ = ∫ t in Set.Icc (0 : Real) A,
              (A - t) ^ m / ((Nat.factorial m : Nat) : Real) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht
          exact ih (A - t) (by linarith [ht.2])
        _ = A ^ (m + 1) / ((Nat.factorial (m + 1) : Nat) : Real) :=
          OAI.PiExponent.DeterminantContradiction.standardSimplex_explicitBounds_power_integral m A hA