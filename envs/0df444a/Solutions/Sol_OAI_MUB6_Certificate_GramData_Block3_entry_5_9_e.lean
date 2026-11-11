-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_5_9_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:37:53.226689+00:00
-- url     : https://prove2.me/submissions/96f058d6-a5ee-4808-a4cd-6964efecddbc

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

theorem entry_5_9_e_oai : Z 5 9 =
    ∑ k : Fin 27, lowerUnit entries k 5 * D k * lowerUnit entries k 9 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_5_9_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_5_9_e_oai
