-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_24_1_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T12:52:50.976545+00:00
-- url     : https://prove2.me/submissions/e2ec01b6-5ba3-461c-871f-e4d7b600e4dd

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_24_1_e_oai : Z 24 1 =
    ∑ k : Fin 27, lowerUnit entries k 24 * D k * lowerUnit entries k 1 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_24_1_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_24_1_e_oai
