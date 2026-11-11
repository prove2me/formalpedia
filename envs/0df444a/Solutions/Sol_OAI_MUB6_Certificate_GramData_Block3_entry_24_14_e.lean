-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_24_14_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:29:12.583515+00:00
-- url     : https://prove2.me/submissions/79d4edd7-413a-4997-81f7-31d17e1016c3

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_24_14_e_oai : Z 24 14 =
    ∑ k : Fin 27, lowerUnit entries k 24 * D k * lowerUnit entries k 14 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_24_14_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_24_14_e_oai
