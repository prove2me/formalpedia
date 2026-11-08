-- Prove2me | solution 1 for OAI.SharpPlanar.tailScalar_summable_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T19:47:27.66372+00:00
-- url     : https://prove2.me/submissions/0beca3b0-4cf2-4490-821e-76f65e5a829e

import Mathlib
import Definitions.Def_OAIQ098G001
import Theorems.Thm_OAI_SharpPlanar_X_summable_g

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
lemma tailScalar_summable_g_oai (x : X) (N : ℕ) :
    Summable (fun k : Node × Bool => if N<k.1.val then |x k| else 0) := by
  apply Summable.of_nonneg_of_le (fun k => by split_ifs <;> positivity) _ (X_summable_g x)
  intro k
  split_ifs <;> simp [abs_nonneg]
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.tailScalar_summable_g_oai := @OAI.SharpPlanar.tailScalar_summable_g_oai
