-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_14_20_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:01:05.229716+00:00
-- url     : https://prove2.me/submissions/7ff0463a-0b47-4eb7-90d4-10a5ebf62162

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_14_20_e_oai : Z 14 20 =
    ∑ k : Fin 27, lowerUnit entries k 14 * D k * lowerUnit entries k 20 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_14_20_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_14_20_e_oai
