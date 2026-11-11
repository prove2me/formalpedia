-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_12_15_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T08:57:11.036334+00:00
-- url     : https://prove2.me/submissions/e50a7281-a6d6-4403-af05-516efa4e0b5a

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_12_15_e_oai : Z 12 15 =
    ∑ k : Fin 27, lowerUnit entries k 12 * D k * lowerUnit entries k 15 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_12_15_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_12_15_e_oai
