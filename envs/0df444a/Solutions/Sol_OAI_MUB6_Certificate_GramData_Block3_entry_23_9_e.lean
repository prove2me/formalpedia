-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_23_9_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:29:43.999187+00:00
-- url     : https://prove2.me/submissions/f8c45888-2637-4101-953a-e16600c91759

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_23_9_e_oai : Z 23 9 =
    ∑ k : Fin 27, lowerUnit entries k 23 * D k * lowerUnit entries k 9 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_23_9_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_23_9_e_oai
