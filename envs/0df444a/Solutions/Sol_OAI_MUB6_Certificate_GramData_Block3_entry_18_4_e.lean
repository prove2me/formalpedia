-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_18_4_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:09:37.612138+00:00
-- url     : https://prove2.me/submissions/f7242350-1b58-4d9e-84a6-b64daaae79e0

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_18_4_e_oai : Z 18 4 =
    ∑ k : Fin 27, lowerUnit entries k 18 * D k * lowerUnit entries k 4 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_18_4_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_18_4_e_oai
