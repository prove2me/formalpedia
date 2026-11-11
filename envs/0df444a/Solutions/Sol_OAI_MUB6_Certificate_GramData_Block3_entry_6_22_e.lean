-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_6_22_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:39:44.141719+00:00
-- url     : https://prove2.me/submissions/57652df2-bdc6-42f2-a452-3026dbf8c500

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

theorem entry_6_22_e_oai : Z 6 22 =
    ∑ k : Fin 27, lowerUnit entries k 6 * D k * lowerUnit entries k 22 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_6_22_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_6_22_e_oai
