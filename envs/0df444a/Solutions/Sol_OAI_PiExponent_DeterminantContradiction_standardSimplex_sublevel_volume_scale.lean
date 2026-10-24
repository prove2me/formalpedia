-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.standardSimplex_sublevel_volume_scale
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T06:56:25.904217+00:00
-- url     : https://prove2.me/submissions/38b0aeb9-db60-417f-8984-2116eb6cf37a

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_standardSimplex_sublevel_volume_scale_ennreal
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem solution {m : Nat} (A : Real) (hA : 0 < A) :
    (MeasureTheory.volume {x : Fin m → Real | (∀ i : Fin m, 0 ≤ x i) ∧
      ∑ i : Fin m, x i ≤ A}).toReal = A ^ m *
        (MeasureTheory.volume {x : Fin m → Real | (∀ i : Fin m, 0 ≤ x i) ∧
          ∑ i : Fin m, x i ≤ 1}).toReal := by
  have h := standardSimplex_sublevel_volume_scale_ennreal (m := m) A hA
  have ht := congrArg ENNReal.toReal h
  simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal, hA.le] using ht