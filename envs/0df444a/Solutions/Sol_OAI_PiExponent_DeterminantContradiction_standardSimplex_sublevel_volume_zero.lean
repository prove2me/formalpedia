-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.standardSimplex_sublevel_volume_zero
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T07:06:49.972438+00:00
-- url     : https://prove2.me/submissions/6c8953b3-109b-4e58-9d3f-f41761630f8e

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem solution :
    (MeasureTheory.volume {x : Fin 0 → Real | (∀ i : Fin 0, 0 ≤ x i) ∧
      ∑ i : Fin 0, x i ≤ 1}).toReal = 1 := by
  have hset : {x : Fin 0 → Real | (∀ i : Fin 0, 0 ≤ x i) ∧
      ∑ i : Fin 0, x i ≤ 1} = Set.univ := by
    ext x
    simp
  rw [hset]
  simp [MeasureTheory.volume_pi, MeasureTheory.Measure.pi_of_empty]