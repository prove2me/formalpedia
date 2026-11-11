-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_18_18_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:08:54.386236+00:00
-- url     : https://prove2.me/submissions/2a7cb560-dec3-4ca8-90fd-875815e6f6ee

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

theorem entry_18_18_e_oai : Z 18 18 =
    ∑ k : Fin 27, lowerUnit entries k 18 * D k * lowerUnit entries k 18 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_18_18_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_18_18_e_oai
