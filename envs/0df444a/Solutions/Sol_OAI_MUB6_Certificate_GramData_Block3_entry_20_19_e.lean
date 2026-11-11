-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_20_19_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:23:00.609679+00:00
-- url     : https://prove2.me/submissions/9750862b-e4df-46a9-b7df-81b55e5cf8e3

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_20_19_e_oai : Z 20 19 =
    ∑ k : Fin 27, lowerUnit entries k 20 * D k * lowerUnit entries k 19 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_20_19_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_20_19_e_oai
