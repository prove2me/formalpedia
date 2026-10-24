-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_volume_succ
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T07:21:48.861589+00:00
-- url     : https://prove2.me/submissions/d3663633-113c-4081-81e7-6a06081b6780

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_volume_eq_inv_factorial

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem solution (n : Nat) :
    (MeasureTheory.volume {x : Fin (n + 1) -> Real | (forall i : Fin (n + 1), 0 <= x i) /\
      Finset.univ.sum (fun i : Fin (n + 1) => x i) <= 1}).toReal =
      ((MeasureTheory.volume {x : Fin n -> Real | (forall i : Fin n, 0 <= x i) /\
        Finset.univ.sum (fun i : Fin n => x i) <= 1}).toReal) / ((n + 1 : Nat) : Real) := by
  rw [OAI.PiExponent.DeterminantContradiction.simplex_volume_eq_inv_factorial,
      OAI.PiExponent.DeterminantContradiction.simplex_volume_eq_inv_factorial]
  have hfac : ((Nat.factorial (n + 1) : Nat) : Real) =
      ((n + 1 : Nat) : Real) * ((Nat.factorial n : Nat) : Real) := by
    simp [Nat.factorial_succ]
  rw [hfac]
  have hn : Not (((n + 1 : Nat) : Real) = 0) := by positivity
  have hfact : Not (((Nat.factorial n : Nat) : Real) = 0) := by
    exact_mod_cast (Nat.factorial_ne_zero n)
  field_simp [hn, hfact] <;> ring