-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.actual_minor_uniform_exp_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-07T19:51:15.417753+00:00
-- url     : https://prove2.me/submissions/a83bac8c-ec97-4218-8fbd-c8cd3260e342
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_matrix_det_norm_le_prod_row_sum
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actual_minor_row_l1_exp_bound

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem solution
    {nu : Real} (d : FixedData nu) (hnu : 0 <= nu)
    {H : Real} (hH : 0 < H) (selection : Row d H -> Column d H) :
    norm (actualMinor d H selection).det <=
      Real.exp ((actualRowCount d H : Real) * H *
        (d.analyticError + analyticRemainder d H +
          max (-collisionRate d H)
            (-nu * ((d.base.A : Real) * (1 - d.base.eta) - actualMean d H)))) := by
  classical
  let C : Real := d.analyticError + analyticRemainder d H +
    max (-collisionRate d H)
      (-nu * ((d.base.A : Real) * (1 - d.base.eta) - actualMean d H))
  have hdet := matrix_det_norm_le_prod_row_sum (actualMinor d H selection)
  have hrows :
      (∏ rowIdx : Row d H, ∑ colIdx : Row d H,
        norm ((actualMinor d H selection) rowIdx colIdx)) <=
      ∏ rowIdx : Row d H, Real.exp (H * C) := by
    apply Finset.prod_le_prod
    · intro rowIdx hrow
      exact Finset.sum_nonneg fun colIdx hcol => norm_nonneg _
    · intro rowIdx hrow
      simpa [C] using
        actual_minor_row_l1_exp_bound d hnu hH selection rowIdx
  have hconst :
      (∏ rowIdx : Row d H, Real.exp (H * C)) =
        Real.exp ((actualRowCount d H : Real) * H * C) := by
    rw [Finset.prod_const, ← Real.exp_nat_mul]
    simp [actualRowCount, mul_assoc]
  calc
    norm (actualMinor d H selection).det <=
        ∏ rowIdx : Row d H, ∑ colIdx : Row d H,
          norm ((actualMinor d H selection) rowIdx colIdx) := hdet
    _ <= ∏ rowIdx : Row d H, Real.exp (H * C) := hrows
    _ = Real.exp ((actualRowCount d H : Real) * H * C) := hconst
    _ = Real.exp ((actualRowCount d H : Real) * H *
        (d.analyticError + analyticRemainder d H +
          max (-collisionRate d H)
            (-nu * ((d.base.A : Real) * (1 - d.base.eta) - actualMean d H)))) := by
      simp [C]
