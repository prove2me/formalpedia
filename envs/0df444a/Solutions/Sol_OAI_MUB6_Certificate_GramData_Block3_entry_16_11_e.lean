-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_16_11_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T20:39:56.093122+00:00
-- url     : https://prove2.me/submissions/6bc9079d-7f74-430b-bb4f-61b4272babca

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_16_11_e_oai : Z 16 11 =
    ∑ k : Fin 27, lowerUnit entries k 16 * D k * lowerUnit entries k 11 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_16_11_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_16_11_e_oai
