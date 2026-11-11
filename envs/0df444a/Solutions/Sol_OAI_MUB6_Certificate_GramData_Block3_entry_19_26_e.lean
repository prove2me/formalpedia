-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_19_26_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:17:21.05079+00:00
-- url     : https://prove2.me/submissions/c1f70ef1-7254-4aa1-a2bf-b2c9964ce9ac

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_19_26_e_oai : Z 19 26 =
    ∑ k : Fin 27, lowerUnit entries k 19 * D k * lowerUnit entries k 26 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_19_26_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_19_26_e_oai
