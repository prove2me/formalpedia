-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_25_0_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T12:54:50.217195+00:00
-- url     : https://prove2.me/submissions/6900cf83-76ec-40fc-9354-a6d34312afd5

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_25_0_e_oai : Z 25 0 =
    ∑ k : Fin 27, lowerUnit entries k 25 * D k * lowerUnit entries k 0 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_25_0_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_25_0_e_oai
