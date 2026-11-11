-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_20_12_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:20:33.662581+00:00
-- url     : https://prove2.me/submissions/d5d957d7-7bc6-4218-b9a6-39530936ec72

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

theorem entry_20_12_e_oai : Z 20 12 =
    ∑ k : Fin 27, lowerUnit entries k 20 * D k * lowerUnit entries k 12 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_20_12_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_20_12_e_oai
