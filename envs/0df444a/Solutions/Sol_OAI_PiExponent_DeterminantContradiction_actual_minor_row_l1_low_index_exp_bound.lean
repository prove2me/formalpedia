-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.actual_minor_row_l1_low_index_exp_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-07T20:54:11.510184+00:00
-- url     : https://prove2.me/submissions/ef8e8f41-2047-4977-8a3b-27f9b1ccb54a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actual_matrix_entry_low_index_exp_bound

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem solution
    {nu : Real} (d : FixedData nu) (hnu : 0 <= nu)
    {H : Real} (hH : 0 < H) (selection : Row d H -> Column d H)
    (rowIdx : Row d H) :
    Finset.sum Finset.univ (fun colIdx : Row d H =>
      norm ((actualMinor d H selection) rowIdx colIdx)) <=
      Real.exp (H * (d.analyticError + analyticRemainder d H +
        -nu * ((d.base.A : Real) * (1 - d.base.eta) - actualMean d H))) := by
  classical
  have hentry (colIdx : Row d H) :
      norm ((actualMinor d H selection) rowIdx colIdx) <=
        Real.exp (H * (d.analyticError + analyticRemainder d H +
          -nu * ((d.base.A : Real) * (1 - d.base.eta) - actualMean d H) -
          Real.log (actualRowCount d H : Real) / H)) := by
    simpa [actualMinor, MatrixArithmetic.selectedMinor, actualMatrix] using
      actual_matrix_entry_low_index_exp_bound d hnu hH rowIdx (selection colIdx)
  have hrows : Nonempty (Row d H) := by
    refine ⟨⟨⟨0, Nat.zero_lt_of_lt d.K_pos⟩, ⟨0, ?_⟩⟩⟩
    change (0 : Fin (d.m + 1) -> Nat) ∈ strictWeightedSimplex
      (InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d))) H
    simp [strictWeightedSimplex, realWeightedSimplex]
    exact ⟨hH.le, hH⟩
  have hN : (0 : Real) < (actualRowCount d H : Real) := by
    unfold actualRowCount
    exact_mod_cast (Fintype.card_pos_iff.mpr hrows)
  calc
    Finset.sum Finset.univ (fun colIdx : Row d H =>
        norm ((actualMinor d H selection) rowIdx colIdx)) <=
      Finset.sum Finset.univ (fun _ : Row d H =>
        Real.exp (H * (d.analyticError + analyticRemainder d H +
          -nu * ((d.base.A : Real) * (1 - d.base.eta) - actualMean d H) -
          Real.log (actualRowCount d H : Real) / H))) := by
        exact Finset.sum_le_sum fun colIdx _ => hentry colIdx
    _ = (actualRowCount d H : Real) *
        Real.exp (H * (d.analyticError + analyticRemainder d H +
          -nu * ((d.base.A : Real) * (1 - d.base.eta) - actualMean d H) -
          Real.log (actualRowCount d H : Real) / H)) := by
        simp [actualRowCount, Finset.sum_const, nsmul_eq_mul]
    _ = Real.exp (H * (d.analyticError + analyticRemainder d H +
          -nu * ((d.base.A : Real) * (1 - d.base.eta) - actualMean d H))) := by
        rw [← Real.exp_log hN, ← Real.exp_add]
        congr 1
        have hHne : H ≠ 0 := ne_of_gt hH
        simp only [Real.log_exp]
        field_simp
        ring_nf
