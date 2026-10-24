-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weightedSimplex_explicit_bounds_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T19:39:14.031361+00:00
-- url     : https://prove2.me/submissions/a86b2086-167f-4b96-9c6b-f0e231fcd255

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_explicit_bounds_tendsto_for_volume
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem solution {m : Nat} (w : Fin m → Real) (A : Real) (hw : ∀ i, 0 < w i) (hA : 0 < A) :
    Tendsto (fun H : Real => (A - (∑ i : Fin m, w i) / H) ^ m /
        ((Nat.factorial m : Nat) : Real) / ∏ i : Fin m, w i) atTop
      (nhds ((MeasureTheory.volume {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, w i * x i ≤ A}).toReal)) ∧
    Tendsto (fun H : Real => (A + (∑ i : Fin m, w i) / H) ^ m /
        ((Nat.factorial m : Nat) : Real) / ∏ i : Fin m, w i) atTop
      (nhds ((MeasureTheory.volume {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, w i * x i ≤ A}).toReal)) := by
  apply OAI.PiExponent.DeterminantContradiction.weightedSimplex_explicit_bounds_tendsto_for_volume <;> assumption
