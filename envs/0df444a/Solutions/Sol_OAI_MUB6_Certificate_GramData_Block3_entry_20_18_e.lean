-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_20_18_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:22:59.395642+00:00
-- url     : https://prove2.me/submissions/9a6d0db7-ddee-42ba-a062-e2c25e89c4d9

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

theorem entry_20_18_e_oai : Z 20 18 =
    ∑ k : Fin 27, lowerUnit entries k 20 * D k * lowerUnit entries k 18 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_20_18_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_20_18_e_oai
