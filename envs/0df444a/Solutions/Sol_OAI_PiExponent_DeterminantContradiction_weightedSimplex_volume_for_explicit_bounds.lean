-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weightedSimplex_volume_for_explicit_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T14:46:07.077513+00:00
-- url     : https://prove2.me/submissions/83faa511-7ee2-4ed8-9246-fbe7f8c1988c

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplex_volume_for_explicit_bounds
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_volume_eq_standardSimplex_div_prod

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem solution {m : Nat} (w : Fin m → Real) (A : Real)
    (hw : ∀ i, 0 < w i) (hA : 0 < A) :
    (MeasureTheory.volume {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧
      ∑ i : Fin m, w i * x i ≤ A}).toReal =
      A ^ m / ((Nat.factorial m : Nat) : Real) / ∏ i : Fin m, w i := by
  rw [OAI.PiExponent.DeterminantContradiction.weightedSimplex_volume_eq_standardSimplex_div_prod
    w A hw hA.le]
  rw [OAI.PiExponent.DeterminantContradiction.standardSimplex_volume_for_explicit_bounds
    (m := m) A hA.le]
