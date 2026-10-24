-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weightedSimplex_explicit_bounds_tendsto_for_volume
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T14:39:11.950789+00:00
-- url     : https://prove2.me/submissions/a65a9b57-bd4f-4d6a-9726-7c997006bb4d

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedSimplex_volume_for_explicit_bounds
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_explicit_scalar_bounds_tendsto_for_volume
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem solution {m : Nat} (w : Fin m → Real) (A : Real)
    (hw : ∀ i, 0 < w i) (hA : 0 < A) :
    Tendsto (fun H : Real => (A - (∑ i : Fin m, w i) / H) ^ m /
        ((Nat.factorial m : Nat) : Real) / ∏ i : Fin m, w i) atTop
      (nhds ((MeasureTheory.volume {x : Fin m → Real |
        (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, w i * x i ≤ A}).toReal)) ∧
    Tendsto (fun H : Real => (A + (∑ i : Fin m, w i) / H) ^ m /
        ((Nat.factorial m : Nat) : Real) / ∏ i : Fin m, w i) atTop
      (nhds ((MeasureTheory.volume {x : Fin m → Real |
        (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, w i * x i ≤ A}).toReal)) := by
  rw [OAI.PiExponent.DeterminantContradiction.weightedSimplex_volume_for_explicit_bounds
    w A hw hA]
  exact OAI.PiExponent.DeterminantContradiction.explicit_scalar_bounds_tendsto_for_volume
    w A hw