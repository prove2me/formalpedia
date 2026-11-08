-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_9_1_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T20:45:18.998514+00:00
-- url     : https://prove2.me/submissions/8848ceaa-6cd4-4a89-a4ca-d0a2fc1cb514

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_9_1_e_oai : Z 9 1 =
    ∑ k : Fin 27, lowerUnit entries k 9 * D k * lowerUnit entries k 1 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_9_1_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_9_1_e_oai
