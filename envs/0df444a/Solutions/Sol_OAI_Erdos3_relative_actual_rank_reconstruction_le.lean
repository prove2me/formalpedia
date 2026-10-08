-- Prove2me | solution 1 for OAI.Erdos3.relative_actual_rank_reconstruction_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T10:22:06.980099+00:00
-- url     : https://prove2.me/submissions/b81c01fd-866f-4cd1-abcf-d30d52ca1a59

import Mathlib
import Definitions.Def_ErdosReciprocal

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RelativeActualRankBudget
namespace OAI

section

namespace Erdos3

theorem relative_actual_rank_reconstruction_le
    {s d d₀ old removed : ℕ} (hremoved : removed ≤ old)
    (hreturned : d ≤ d₀ + s * (old - removed)) :
    d + s * removed ≤ d₀ + s * old := by
  calc
    d + s * removed ≤ d₀ + s * (old - removed) + s * removed :=
      Nat.add_le_add_right hreturned _
    _ = d₀ + s * old := by
      rw [Nat.add_assoc, ← Nat.mul_add, Nat.sub_add_cancel hremoved]

end Erdos3

end

end OAI

end

theorem solution : type_of% @OAI.Erdos3.relative_actual_rank_reconstruction_le := @OAI.Erdos3.relative_actual_rank_reconstruction_le
