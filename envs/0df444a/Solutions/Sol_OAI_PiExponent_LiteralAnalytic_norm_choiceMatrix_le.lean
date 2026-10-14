-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.norm_choiceMatrix_le
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T10:27:03.643372+00:00
-- url     : https://prove2.me/submissions/9007a099-9e67-4e18-bedd-f5cd54a75dd1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_norm_choiceMatrix_le_of_permutation_sum
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_norm_det_le_permutation_sum

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.LiteralAnalytic OAI.PiExponent.DeterminantContradiction

theorem solution {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H)
    (selection : Row d H → Column d H) (f : ChoiceFamily d H) :
    ‖(choiceMatrix d selection f).det‖ ≤ Real.exp
      (-(Real.log 2 / 4) * (∑ A : Transverse d H,
        (Collision.multiplicity Finset.univ (fun r => (f r).1) A : ℝ) ^ 2) +
        (actualRowCount d H : ℝ) * H *
          (d.holomorphicError + Collision.collisionRemainder (actualRowCount d H) H)) := by
  have hperm := OAI.PiExponent.LiteralAnalytic.norm_choiceMatrix_le_of_permutation_sum
    d hH selection f
  have hdet := OAI.PiExponent.LiteralAnalytic.norm_det_le_permutation_sum
    (choiceMatrix d selection f)
  calc
    ‖(choiceMatrix d selection f).det‖ ≤
        ∑ σ : Equiv.Perm (Row d H), ∏ r : Row d H,
          ‖choiceMatrix d selection f r (σ r)‖ := hdet
    _ ≤ Real.exp
        (-(Real.log 2 / 4) *
          (∑ A : Transverse d H,
            (Collision.multiplicity Finset.univ (fun r => (f r).1) A : ℝ) ^ 2) +
          (actualRowCount d H : ℝ) *
            (H * d.holomorphicError + Real.log (actualRowCount d H : ℝ) +
              Real.log 2 / 4 - Real.log (1 - Collision.collisionRatio))) := hperm
    _ = Real.exp
        (-(Real.log 2 / 4) *
          (∑ A : Transverse d H,
            (Collision.multiplicity Finset.univ (fun r => (f r).1) A : ℝ) ^ 2) +
          (actualRowCount d H : ℝ) * H *
            (d.holomorphicError + Collision.collisionRemainder (actualRowCount d H) H)) := by
      congr 1
      unfold Collision.collisionRemainder
      field_simp [ne_of_gt hH]
      <;> ring
