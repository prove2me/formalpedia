-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_26_11_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T12:57:27.995712+00:00
-- url     : https://prove2.me/submissions/8e792e0f-4660-47f8-9d01-0e7c9e4053fb

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check29
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_26_11_e_oai : Z 26 11 =
    ∑ k : Fin 27, lowerUnit entries k 26 * D k * lowerUnit entries k 11 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_26_11_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_26_11_e_oai
