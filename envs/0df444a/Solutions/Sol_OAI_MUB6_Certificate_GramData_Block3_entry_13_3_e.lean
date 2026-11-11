-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_13_3_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T08:59:49.218379+00:00
-- url     : https://prove2.me/submissions/5864df3d-67bd-4c1a-8056-4485f3cfb698

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_13_3_e_oai : Z 13 3 =
    ∑ k : Fin 27, lowerUnit entries k 13 * D k * lowerUnit entries k 3 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_13_3_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_13_3_e_oai
