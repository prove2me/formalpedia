-- Prove2me | solution 1 for OAI.SharpPlanar.tailScalar_summable_e
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-04T08:08:08.455803+00:00
-- url     : https://prove2.me/submissions/d80b2f60-59b4-4432-8d6f-1e96ec3577a7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ098E001
import Theorems.Thm_OAI_SharpPlanar_X_summable_e

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FiniteTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Tails of the interpolation operator

Coordinate projections and shell estimates bound the tails of the interpolation operator.
-/

namespace SharpPlanar
open scoped BigOperators
lemma tailScalar_summable_e_oai (x : X) (N : ℕ) :
    Summable (fun k : Node × Bool => if N<k.1.val then |x k| else 0) := by
  apply Summable.of_nonneg_of_le (fun k => by split_ifs <;> positivity) _ (X_summable_e x)
  intro k
  split_ifs <;> simp [abs_nonneg]
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.tailScalar_summable_e_oai := @OAI.SharpPlanar.tailScalar_summable_e_oai
