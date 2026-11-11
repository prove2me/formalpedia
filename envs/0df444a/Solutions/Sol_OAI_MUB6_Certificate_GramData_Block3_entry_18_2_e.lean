-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_18_2_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:08:56.943698+00:00
-- url     : https://prove2.me/submissions/053ab143-caa0-4e86-a6d1-7f5a14a44066

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

theorem entry_18_2_e_oai : Z 18 2 =
    ∑ k : Fin 27, lowerUnit entries k 18 * D k * lowerUnit entries k 2 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_18_2_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_18_2_e_oai
