-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_1_4_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:19:44.788645+00:00
-- url     : https://prove2.me/submissions/2a2a7792-3a98-4d9f-81b2-e425f41180ce

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_1_4_e_oai : Z 1 4 =
    ∑ k : Fin 27, lowerUnit entries k 1 * D k * lowerUnit entries k 4 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_1_4_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_1_4_e_oai
