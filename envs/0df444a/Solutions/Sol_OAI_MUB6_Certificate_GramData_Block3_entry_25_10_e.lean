-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_25_10_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T12:54:14.911725+00:00
-- url     : https://prove2.me/submissions/16f83c95-2964-44f3-a673-c28f1be3b9f6

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

theorem entry_25_10_e_oai : Z 25 10 =
    ∑ k : Fin 27, lowerUnit entries k 25 * D k * lowerUnit entries k 10 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_25_10_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_25_10_e_oai
