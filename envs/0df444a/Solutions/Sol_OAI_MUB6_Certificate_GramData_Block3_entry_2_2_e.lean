-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_2_2_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:31:00.570509+00:00
-- url     : https://prove2.me/submissions/09878827-7146-4528-8063-705a7598ef96

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_2_2_e_oai : Z 2 2 =
    ∑ k : Fin 27, lowerUnit entries k 2 * D k * lowerUnit entries k 2 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_2_2_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_2_2_e_oai
