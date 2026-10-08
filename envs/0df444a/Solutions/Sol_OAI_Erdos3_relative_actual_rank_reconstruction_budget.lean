-- Prove2me | solution 1 for OAI.Erdos3.relative_actual_rank_reconstruction_budget
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T10:22:01.955979+00:00
-- url     : https://prove2.me/submissions/46ad6afd-a5b2-48f1-bf28-43e4de99fce9

import Mathlib
import Definitions.Def_ErdosReciprocal

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RelativeActualRankBudget
namespace OAI

section

namespace Erdos3

theorem relative_actual_rank_reconstruction_budget
    {s d removed bound : ℕ} {childCost p : ℝ}
    (hchild : 0 ≤ childCost) (hd : d ≤ min bound ⌊childCost⌋₊)
    (hremoved : (removed : ℝ) ≤ p) :
    ((d + s * removed : ℕ) : ℝ) ≤ childCost + (s : ℝ) * p := by
  have hdim : (d : ℝ) ≤ childCost :=
    (Nat.cast_le.mpr (hd.trans (min_le_right _ _))).trans (Nat.floor_le hchild)
  simpa only [Nat.cast_add, Nat.cast_mul] using
    add_le_add hdim (mul_le_mul_of_nonneg_left hremoved (Nat.cast_nonneg s))

end Erdos3

end

end OAI

end

theorem solution : type_of% @OAI.Erdos3.relative_actual_rank_reconstruction_budget := @OAI.Erdos3.relative_actual_rank_reconstruction_budget
