-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.standardSimplex_volume_factorial
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T07:18:23.238984+00:00
-- url     : https://prove2.me/submissions/879d4173-3054-4955-9af5-1d9310d7c00c

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_volume_succ
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_volume_zero
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem solution (n : Nat) :
    (MeasureTheory.volume {x : Fin n → Real | (∀ i : Fin n, 0 ≤ x i) ∧
      ∑ i : Fin n, x i ≤ 1}).toReal = 1 / (Nat.factorial n : Real) := by
  induction n with
  | zero =>
      simpa [Nat.factorial_zero] using
        OAI.PiExponent.DeterminantContradiction.simplex_volume_zero
  | succ n ih =>
      calc
        (MeasureTheory.volume {x : Fin (n + 1) → Real |
            (∀ i : Fin (n + 1), 0 ≤ x i) ∧ ∑ i : Fin (n + 1), x i ≤ 1}).toReal =
            ((MeasureTheory.volume {x : Fin n → Real |
              (∀ i : Fin n, 0 ≤ x i) ∧ ∑ i : Fin n, x i ≤ 1}).toReal) /
              ((n + 1 : Nat) : Real) := by
                exact OAI.PiExponent.DeterminantContradiction.simplex_volume_succ n
        _ = (1 / (Nat.factorial n : Real)) / ((n + 1 : Nat) : Real) := by rw [ih]
        _ = 1 / (Nat.factorial (n + 1) : Real) := by
              rw [Nat.factorial_succ]
              push_cast
              have hn : (((n + 1 : Nat) : Real)) ≠ 0 := by positivity
              have hf : ((Nat.factorial n : Nat) : Real) ≠ 0 := by positivity
              field_simp <;> ring