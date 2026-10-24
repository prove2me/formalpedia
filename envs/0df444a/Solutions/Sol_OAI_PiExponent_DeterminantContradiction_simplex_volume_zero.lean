-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_volume_zero
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T07:25:28.324494+00:00
-- url     : https://prove2.me/submissions/fb16e19f-e8a4-46af-a099-b40aaf7675af

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
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