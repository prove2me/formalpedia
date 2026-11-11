-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_14_2_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:21:22.869089+00:00
-- url     : https://prove2.me/submissions/16ad5999-ffb8-4e0e-ba72-abd672b77678

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_14_2_e_oai : Z 14 2 =
    ∑ k : Fin 27, lowerUnit entries k 14 * D k * lowerUnit entries k 2 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_14_2_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_14_2_e_oai
