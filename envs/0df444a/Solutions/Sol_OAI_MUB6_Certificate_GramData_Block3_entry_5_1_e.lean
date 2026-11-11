-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_5_1_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:37:47.471456+00:00
-- url     : https://prove2.me/submissions/b0950f49-6c5b-4b58-9499-f92ba131ad94

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_5_1_e_oai : Z 5 1 =
    ∑ k : Fin 27, lowerUnit entries k 5 * D k * lowerUnit entries k 1 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_5_1_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_5_1_e_oai
