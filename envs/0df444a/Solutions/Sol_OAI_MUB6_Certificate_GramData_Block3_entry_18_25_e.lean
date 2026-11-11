-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_18_25_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:08:58.163042+00:00
-- url     : https://prove2.me/submissions/2d9d7ae0-30cb-4174-ab1e-af2e76c83ca0

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_18_25_e_oai : Z 18 25 =
    ∑ k : Fin 27, lowerUnit entries k 18 * D k * lowerUnit entries k 25 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_18_25_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_18_25_e_oai
