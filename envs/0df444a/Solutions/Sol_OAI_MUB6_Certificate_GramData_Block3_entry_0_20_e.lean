-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_0_20_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T08:53:58.957729+00:00
-- url     : https://prove2.me/submissions/a086eebd-8429-48d9-970f-38740d562be6

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_0_20_e_oai : Z 0 20 =
    ∑ k : Fin 27, lowerUnit entries k 0 * D k * lowerUnit entries k 20 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_0_20_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_0_20_e_oai
