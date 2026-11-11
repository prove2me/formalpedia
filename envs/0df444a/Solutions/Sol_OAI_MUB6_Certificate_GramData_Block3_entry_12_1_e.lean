-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_12_1_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T08:56:31.08226+00:00
-- url     : https://prove2.me/submissions/22170755-1fe5-40cc-b96d-e1582fe7705b

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_12_1_e_oai : Z 12 1 =
    ∑ k : Fin 27, lowerUnit entries k 12 * D k * lowerUnit entries k 1 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_12_1_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_12_1_e_oai
