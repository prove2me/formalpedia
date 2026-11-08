-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_10_0_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T20:33:39.478707+00:00
-- url     : https://prove2.me/submissions/e31718dd-1157-417f-850f-c5c75f5610e7

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_10_0_e_oai : Z 10 0 =
    ∑ k : Fin 27, lowerUnit entries k 10 * D k * lowerUnit entries k 0 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_10_0_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_10_0_e_oai
