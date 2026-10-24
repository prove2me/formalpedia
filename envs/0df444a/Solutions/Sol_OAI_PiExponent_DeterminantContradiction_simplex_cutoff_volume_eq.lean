-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_cutoff_volume_eq
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T07:55:31.75682+00:00
-- url     : https://prove2.me/submissions/87a6bd53-2240-44d6-a937-1b3a18ab0f88

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_cutoff_volume_measure_scaling
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

noncomputable section

theorem solution (n : Nat) (r : Real) (hr : 0 ≤ r) :
    (MeasureTheory.volume {y : Fin n → Real | (∀ i : Fin n, 0 ≤ y i) ∧
      ∑ i : Fin n, y i ≤ r}).toReal =
      (MeasureTheory.volume {y : Fin n → Real | (∀ i : Fin n, 0 ≤ y i) ∧
        ∑ i : Fin n, y i ≤ 1}).toReal * r ^ n := by
  have hscale :=
    OAI.PiExponent.DeterminantContradiction.simplex_cutoff_volume_measure_scaling n r hr
  rw [hscale, ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hr n)]
  ring