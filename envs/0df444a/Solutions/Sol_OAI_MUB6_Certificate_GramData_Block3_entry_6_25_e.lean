-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_6_25_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:40:19.073608+00:00
-- url     : https://prove2.me/submissions/e4e184c7-5229-41d4-a0b1-5a428bf2b903

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_6_25_e_oai : Z 6 25 =
    ∑ k : Fin 27, lowerUnit entries k 6 * D k * lowerUnit entries k 25 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_6_25_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_6_25_e_oai
