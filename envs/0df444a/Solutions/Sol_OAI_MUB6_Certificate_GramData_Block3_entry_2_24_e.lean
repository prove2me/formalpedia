-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_2_24_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:31:43.159516+00:00
-- url     : https://prove2.me/submissions/3efad404-a015-427c-a3ba-f58d2038a5d7

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_2_24_e_oai : Z 2 24 =
    ∑ k : Fin 27, lowerUnit entries k 2 * D k * lowerUnit entries k 24 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_2_24_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_2_24_e_oai
