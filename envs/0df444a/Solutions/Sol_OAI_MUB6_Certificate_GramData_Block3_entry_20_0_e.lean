-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_20_0_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:20:26.017896+00:00
-- url     : https://prove2.me/submissions/f1fa8f96-71dc-4d58-9075-f7b296be67c8

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_20_0_e_oai : Z 20 0 =
    ∑ k : Fin 27, lowerUnit entries k 20 * D k * lowerUnit entries k 0 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_20_0_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_20_0_e_oai
