-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_volume_zero_measure
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T07:42:10.917721+00:00
-- url     : https://prove2.me/submissions/1a095c7f-8b15-44ae-bba5-b3cfa19c3ff0

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem solution :
    (MeasureTheory.volume {x : Fin 0 → Real | (∀ i : Fin 0, 0 ≤ x i) ∧
      ∑ i : Fin 0, x i ≤ 1}).toReal = 1 / (Nat.factorial 0 : Real) := by
  have hs : {x : Fin 0 → Real | (∀ i : Fin 0, 0 ≤ x i) ∧
      ∑ i : Fin 0, x i ≤ 1} = Set.univ := by
    ext x
    simp
  rw [hs, MeasureTheory.Measure.volume_pi_eq_dirac]
  norm_num [Nat.factorial]