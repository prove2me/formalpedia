-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_22_3_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:27:08.171254+00:00
-- url     : https://prove2.me/submissions/fb3ffb9e-fc05-4c81-aae1-06404d8df2de

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_22_3_e_oai : Z 22 3 =
    ∑ k : Fin 27, lowerUnit entries k 22 * D k * lowerUnit entries k 3 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_22_3_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_22_3_e_oai
