-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_8_22_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T20:44:12.241784+00:00
-- url     : https://prove2.me/submissions/16ebc720-4e87-44e4-ad64-475e36fd9d3f

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

theorem entry_8_22_e_oai : Z 8 22 =
    ∑ k : Fin 27, lowerUnit entries k 8 * D k * lowerUnit entries k 22 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_8_22_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_8_22_e_oai
