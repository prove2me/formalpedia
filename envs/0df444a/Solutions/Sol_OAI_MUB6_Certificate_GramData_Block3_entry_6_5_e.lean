-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_6_5_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:39:45.365446+00:00
-- url     : https://prove2.me/submissions/e0ce5985-81a4-49d5-a275-313790ed0e99

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

theorem entry_6_5_e_oai : Z 6 5 =
    ∑ k : Fin 27, lowerUnit entries k 6 * D k * lowerUnit entries k 5 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_6_5_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_6_5_e_oai
