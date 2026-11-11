-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_22_16_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T12:52:09.859032+00:00
-- url     : https://prove2.me/submissions/3dcb00be-9440-47da-99b7-802cb9d45df8

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

theorem entry_22_16_e_oai : Z 22 16 =
    ∑ k : Fin 27, lowerUnit entries k 22 * D k * lowerUnit entries k 16 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_22_16_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_22_16_e_oai
