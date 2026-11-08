-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_9_24_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T20:45:56.980022+00:00
-- url     : https://prove2.me/submissions/35ebba9c-b125-4660-8359-f0b1dfd217ec

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_9_24_e_oai : Z 9 24 =
    ∑ k : Fin 27, lowerUnit entries k 9 * D k * lowerUnit entries k 24 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_9_24_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_9_24_e_oai
