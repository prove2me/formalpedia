-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_18_0_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:07:26.316927+00:00
-- url     : https://prove2.me/submissions/3bc9ad90-cf27-4961-ab45-3359c02b9c61

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

theorem entry_18_0_e_oai : Z 18 0 =
    ∑ k : Fin 27, lowerUnit entries k 18 * D k * lowerUnit entries k 0 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_18_0_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_18_0_e_oai
