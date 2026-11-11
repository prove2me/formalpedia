-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_7_2_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:42:10.993373+00:00
-- url     : https://prove2.me/submissions/42fe0bbd-8681-42af-9d30-f3a400b69584

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

theorem entry_7_2_e_oai : Z 7 2 =
    ∑ k : Fin 27, lowerUnit entries k 7 * D k * lowerUnit entries k 2 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_7_2_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_7_2_e_oai
