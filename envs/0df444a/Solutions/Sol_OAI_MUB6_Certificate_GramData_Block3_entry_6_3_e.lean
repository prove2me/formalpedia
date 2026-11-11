-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_6_3_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:40:21.72635+00:00
-- url     : https://prove2.me/submissions/8b153d66-38e3-4b6d-9e35-71f27920f6b4

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_6_3_e_oai : Z 6 3 =
    ∑ k : Fin 27, lowerUnit entries k 6 * D k * lowerUnit entries k 3 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_6_3_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_6_3_e_oai
