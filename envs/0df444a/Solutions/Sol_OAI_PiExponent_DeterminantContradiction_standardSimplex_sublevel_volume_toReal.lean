-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.standardSimplex_sublevel_volume_toReal
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T06:53:00.542501+00:00
-- url     : https://prove2.me/submissions/637a15ea-e1e5-45a7-9522-ddf6ef1d04c4

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplex_sublevel_volume_scale
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplex_sublevel_volume_unit

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem solution {m : Nat} (A : Real) (hA : 0 < A) :
    (MeasureTheory.volume {x : Fin m → Real | (∀ i : Fin m, 0 ≤ x i) ∧
      ∑ i : Fin m, x i ≤ A}).toReal = A ^ m / (m.factorial : Real) := by
  calc
    (MeasureTheory.volume {x : Fin m → Real | (∀ i : Fin m, 0 ≤ x i) ∧
        ∑ i : Fin m, x i ≤ A}).toReal =
      A ^ m * (MeasureTheory.volume {x : Fin m → Real | (∀ i : Fin m, 0 ≤ x i) ∧
        ∑ i : Fin m, x i ≤ 1}).toReal :=
          standardSimplex_sublevel_volume_scale (m := m) A hA
    _ = A ^ m / (m.factorial : Real) := by
      rw [standardSimplex_sublevel_volume_unit (m := m)]
      ring