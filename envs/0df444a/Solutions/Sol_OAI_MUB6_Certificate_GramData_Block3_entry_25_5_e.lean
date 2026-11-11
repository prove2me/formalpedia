-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_25_5_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T12:56:17.102105+00:00
-- url     : https://prove2.me/submissions/c185cab7-e522-424d-8a3c-ff8323ffdd94

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

theorem entry_25_5_e_oai : Z 25 5 =
    ∑ k : Fin 27, lowerUnit entries k 25 * D k * lowerUnit entries k 5 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_25_5_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_25_5_e_oai
