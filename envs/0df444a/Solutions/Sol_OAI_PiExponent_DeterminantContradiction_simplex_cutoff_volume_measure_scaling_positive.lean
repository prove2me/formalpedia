-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_cutoff_volume_measure_scaling_positive
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T08:03:54.26661+00:00
-- url     : https://prove2.me/submissions/b0e2ceb1-33b2-48d3-a383-1ee44bc05585

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_cutoff_eq_scalar_preimage
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_volume_scalar_preimage

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem solution
    (n : Nat) (r : Real) (hr : 0 ≤ r) (hpos : 0 < r) :
    MeasureTheory.volume {y : Fin n → Real | (∀ i : Fin n, 0 ≤ y i) ∧
      ∑ i : Fin n, y i ≤ r} =
      ENNReal.ofReal (r ^ n) *
        MeasureTheory.volume {y : Fin n → Real | (∀ i : Fin n, 0 ≤ y i) ∧
          ∑ i : Fin n, y i ≤ 1} := by
  rw [OAI.PiExponent.DeterminantContradiction.simplex_cutoff_eq_scalar_preimage
    n r hr hpos]
  exact OAI.PiExponent.DeterminantContradiction.volume_scalar_preimage
    n r hpos _
