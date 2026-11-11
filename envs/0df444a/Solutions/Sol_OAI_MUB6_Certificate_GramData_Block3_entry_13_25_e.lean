-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_13_25_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:21:17.459191+00:00
-- url     : https://prove2.me/submissions/380f2453-7e34-4c91-847a-1f0cadf52c5f

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_13_25_e_oai : Z 13 25 =
    ∑ k : Fin 27, lowerUnit entries k 13 * D k * lowerUnit entries k 25 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_13_25_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_13_25_e_oai
