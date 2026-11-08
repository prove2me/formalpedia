-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_9_18_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T20:45:37.603264+00:00
-- url     : https://prove2.me/submissions/52dab809-058e-4dfb-b1ae-694c9414a382

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_9_18_e_oai : Z 9 18 =
    ∑ k : Fin 27, lowerUnit entries k 9 * D k * lowerUnit entries k 18 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_9_18_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_9_18_e_oai
