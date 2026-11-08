-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_15_18_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T20:38:42.289988+00:00
-- url     : https://prove2.me/submissions/77ba5253-0c21-43a4-a592-46ebf464aeba

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_15_18_e_oai : Z 15 18 =
    ∑ k : Fin 27, lowerUnit entries k 15 * D k * lowerUnit entries k 18 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_15_18_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_15_18_e_oai
