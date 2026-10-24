-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_coordinate_volume_zero
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T08:04:25.577148+00:00
-- url     : https://prove2.me/submissions/a4822bdb-0592-4f4a-9e5f-795d25537a29

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem solution :
    (MeasureTheory.volume {x : Fin 0 → Real | (∀ i : Fin 0, 0 ≤ x i) ∧
      ∑ i : Fin 0, x i ≤ 1}).toReal = 1 / (Nat.factorial 0 : Real) := by
  have hset : {x : Fin 0 → Real | (∀ i : Fin 0, 0 ≤ x i) ∧
      ∑ i : Fin 0, x i ≤ 1} = Set.univ := by
    ext x
    simp
  rw [hset, MeasureTheory.volume_pi]
  simp [MeasureTheory.Measure.pi_of_empty]