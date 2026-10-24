-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_coordinate_scaled_section_integral
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T07:51:56.174621+00:00
-- url     : https://prove2.me/submissions/1dd208ac-bf33-4be0-9b26-0648160f2e02

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_cutoff_volume_eq
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem solution (n : Nat) :
    (∫ t in (0 : Real)..1, (MeasureTheory.volume {y : Fin n → Real |
      (∀ i : Fin n, 0 ≤ y i) ∧ ∑ i : Fin n, y i ≤ 1 - t}).toReal) =
      (MeasureTheory.volume {y : Fin n → Real | (∀ i : Fin n, 0 ≤ y i) ∧
        ∑ i : Fin n, y i ≤ 1}).toReal *
        (∫ t in (0 : Real)..1, (1 - t) ^ n) := by
  let V := (MeasureTheory.volume {y : Fin n → Real | (∀ i : Fin n, 0 ≤ y i) ∧
    ∑ i : Fin n, y i ≤ 1}).toReal
  calc
    (∫ t in (0 : Real)..1, (MeasureTheory.volume {y : Fin n → Real |
        (∀ i : Fin n, 0 ≤ y i) ∧ ∑ i : Fin n, y i ≤ 1 - t}).toReal) =
        ∫ t in (0 : Real)..1, V * (1 - t) ^ n := by
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp [V]
      have ht1 : t ≤ 1 := by simpa using ht.2
      exact OAI.PiExponent.DeterminantContradiction.simplex_cutoff_volume_eq
        n (1 - t) (sub_nonneg.mpr ht1)
    _ = V * (∫ t in (0 : Real)..1, (1 - t) ^ n) := by
      rw [intervalIntegral.integral_const_mul]