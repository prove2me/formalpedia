-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_19_7_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:17:26.918527+00:00
-- url     : https://prove2.me/submissions/9a5f0337-7d5c-4077-b895-72093861588b

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_19_7_e_oai : Z 19 7 =
    ∑ k : Fin 27, lowerUnit entries k 19 * D k * lowerUnit entries k 7 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_19_7_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_19_7_e_oai
