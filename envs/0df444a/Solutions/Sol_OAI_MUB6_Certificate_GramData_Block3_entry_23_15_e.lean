-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_23_15_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:27:12.556456+00:00
-- url     : https://prove2.me/submissions/68c64a93-1d8a-45b7-b4a4-2df0409ade73

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_23_15_e_oai : Z 23 15 =
    ∑ k : Fin 27, lowerUnit entries k 23 * D k * lowerUnit entries k 15 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_23_15_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_23_15_e_oai
