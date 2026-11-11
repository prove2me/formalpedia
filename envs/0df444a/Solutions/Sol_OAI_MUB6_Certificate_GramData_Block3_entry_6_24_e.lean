-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_6_24_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:40:18.000958+00:00
-- url     : https://prove2.me/submissions/18b6f80c-4dd3-4d64-9c37-9c36057668e5

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_6_24_e_oai : Z 6 24 =
    ∑ k : Fin 27, lowerUnit entries k 6 * D k * lowerUnit entries k 24 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_6_24_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_6_24_e_oai
