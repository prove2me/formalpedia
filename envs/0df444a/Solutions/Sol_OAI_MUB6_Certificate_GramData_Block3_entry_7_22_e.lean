-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_7_22_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:42:45.249421+00:00
-- url     : https://prove2.me/submissions/7d05731a-5e38-4ade-b229-96a19b2cac9e

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_7_22_e_oai : Z 7 22 =
    ∑ k : Fin 27, lowerUnit entries k 7 * D k * lowerUnit entries k 22 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_7_22_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_7_22_e_oai
