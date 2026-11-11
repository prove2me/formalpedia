-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_16_2_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:03:41.138917+00:00
-- url     : https://prove2.me/submissions/711cc9fe-0628-420a-958b-49f2c7cebee8

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

theorem entry_16_2_e_oai : Z 16 2 =
    ∑ k : Fin 27, lowerUnit entries k 16 * D k * lowerUnit entries k 2 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_16_2_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_16_2_e_oai
