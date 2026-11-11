-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_3_9_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:35:18.603097+00:00
-- url     : https://prove2.me/submissions/9c29e846-8add-4aaf-8e8e-2f18f9ad2af0

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_3_9_e_oai : Z 3 9 =
    ∑ k : Fin 27, lowerUnit entries k 3 * D k * lowerUnit entries k 9 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_3_9_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_3_9_e_oai
