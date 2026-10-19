-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.FiniteTranslation.actual_mean_normalization
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T13:31:07.879557+00:00
-- url     : https://prove2.me/submissions/16dbe713-4989-4b1f-a456-f76392f37d0e

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation
import Mathlib.Tactic.FieldSimp

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem solution
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H) :
    (actualRowCount d H : ℝ) * H * actualMean d H =
      MatrixArithmetic.rowWeightedSum d.K d.v0 d.base.theta
        (finiteDenominators d) H := by
  classical
  have hrow : Nonempty (Row d H) := by
    refine ⟨(⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one d.K_pos⟩,
      ⟨fun _ : Fin (d.m + 1) => 0, ?_⟩)⟩
    change (fun _ : Fin (d.m + 1) => 0) ∈
      strictWeightedSimplex
        (InterpolationMatrix.rowWeights d.v0 d.base.theta
          (MatrixArithmetic.logWeights (finiteDenominators d))) H
    simp [strictWeightedSimplex, realWeightedSimplex, hH.le, hH]
  have hcard : (Fintype.card (Row d H) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos_iff.mpr hrow))
  rw [actualRowCount, actualMean, MatrixArithmetic.meanRowWeight]
  field_simp [hcard, ne_of_gt hH]
