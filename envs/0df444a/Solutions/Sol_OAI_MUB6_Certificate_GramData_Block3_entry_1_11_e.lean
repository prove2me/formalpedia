-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_1_11_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:17:33.714905+00:00
-- url     : https://prove2.me/submissions/8ab69263-f339-4ce2-a1d3-22a90232b6da

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_1_11_e_oai : Z 1 11 =
    ∑ k : Fin 27, lowerUnit entries k 1 * D k * lowerUnit entries k 11 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_1_11_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_1_11_e_oai
