-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.actual_weight_sum_eq_row_count_height_mean
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T21:50:03.682129+00:00
-- url     : https://prove2.me/submissions/7e771e69-de23-4093-a114-1704bd48af88

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionTerms
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionWeights

open scoped BigOperators Topology
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion

theorem solution
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H) :
    (actualRowCount d H : ℝ) * H * actualMean d H =
      ∑ r : Row d H,
        ∑ i : Fin d.m,
          MatrixArithmetic.logWeights (finiteDenominators d) i *
            (r.2.1 i.succ : ℝ) := by
  classical
  have hrow : Nonempty (Row d H) := by
    refine ⟨⟨⟨0, lt_of_lt_of_le Nat.zero_lt_one d.K_pos⟩, ⟨0, ?_⟩⟩⟩
    simp [InterpolationMatrix.Row, strictWeightedSimplex, realWeightedSimplex, hH.le, hH]
  have hcard : 0 < (Fintype.card (Row d H) : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr hrow)
  have hden : (Fintype.card (Row d H) : ℝ) * H ≠ 0 :=
    mul_ne_zero hcard.ne' hH.ne'
  simp only [actualRowCount, actualMean, MatrixArithmetic.meanRowWeight]
  rw [div_eq_mul_inv]
  field_simp
  simp [MatrixArithmetic.rowWeightedSum, mul_comm]