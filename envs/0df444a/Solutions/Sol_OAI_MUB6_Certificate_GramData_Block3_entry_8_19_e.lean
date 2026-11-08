-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_8_19_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T20:43:43.186005+00:00
-- url     : https://prove2.me/submissions/13154308-6c8c-4577-b10a-1ad943b1f15c

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

theorem entry_8_19_e_oai : Z 8 19 =
    ∑ k : Fin 27, lowerUnit entries k 8 * D k * lowerUnit entries k 19 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_8_19_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_8_19_e_oai
