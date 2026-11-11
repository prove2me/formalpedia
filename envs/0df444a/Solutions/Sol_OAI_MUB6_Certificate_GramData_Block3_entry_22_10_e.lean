-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_22_10_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:26:29.022732+00:00
-- url     : https://prove2.me/submissions/b8f5c8fc-09c4-4e83-8975-8fffd70e57ca

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_22_10_e_oai : Z 22 10 =
    ∑ k : Fin 27, lowerUnit entries k 22 * D k * lowerUnit entries k 10 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_22_10_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_22_10_e_oai
