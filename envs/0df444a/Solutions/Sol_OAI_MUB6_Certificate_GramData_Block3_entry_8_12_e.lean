-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_8_12_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T20:42:51.501573+00:00
-- url     : https://prove2.me/submissions/ba7e4478-135f-499a-a3ff-6695d499eb5e

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_8_12_e_oai : Z 8 12 =
    ∑ k : Fin 27, lowerUnit entries k 8 * D k * lowerUnit entries k 12 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_8_12_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_8_12_e_oai
