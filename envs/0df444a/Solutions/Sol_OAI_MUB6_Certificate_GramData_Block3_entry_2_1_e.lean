-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_2_1_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:22:13.427915+00:00
-- url     : https://prove2.me/submissions/45290f8f-ba48-4943-a4da-64a24f3e063e

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_2_1_e_oai : Z 2 1 =
    ∑ k : Fin 27, lowerUnit entries k 2 * D k * lowerUnit entries k 1 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_2_1_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_2_1_e_oai
