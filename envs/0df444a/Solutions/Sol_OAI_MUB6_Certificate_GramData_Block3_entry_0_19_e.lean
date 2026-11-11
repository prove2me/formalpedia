-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_0_19_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T08:53:23.617837+00:00
-- url     : https://prove2.me/submissions/c737095c-4a08-4cbe-bf83-4e91a6673fb8

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

theorem entry_0_19_e_oai : Z 0 19 =
    ∑ k : Fin 27, lowerUnit entries k 0 * D k * lowerUnit entries k 19 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_0_19_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_0_19_e_oai
