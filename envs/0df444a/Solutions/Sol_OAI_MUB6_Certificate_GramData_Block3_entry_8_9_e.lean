-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_8_9_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:44:41.093175+00:00
-- url     : https://prove2.me/submissions/dfdaaa4f-875b-4143-a8c2-6687174d9c0b

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_8_9_e_oai : Z 8 9 =
    ∑ k : Fin 27, lowerUnit entries k 8 * D k * lowerUnit entries k 9 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_8_9_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_8_9_e_oai
