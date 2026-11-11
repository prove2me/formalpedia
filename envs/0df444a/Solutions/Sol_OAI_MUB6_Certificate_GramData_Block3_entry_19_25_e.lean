-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_19_25_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:17:19.791142+00:00
-- url     : https://prove2.me/submissions/e36c4b90-0137-4e65-8ee8-919b251e4354

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

theorem entry_19_25_e_oai : Z 19 25 =
    ∑ k : Fin 27, lowerUnit entries k 19 * D k * lowerUnit entries k 25 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_19_25_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_19_25_e_oai
