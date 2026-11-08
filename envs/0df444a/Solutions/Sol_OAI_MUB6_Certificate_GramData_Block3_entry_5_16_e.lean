-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_5_16_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T20:41:44.953189+00:00
-- url     : https://prove2.me/submissions/cf933211-9cf7-48b2-8c77-365906e8d6e3

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_5_16_e_oai : Z 5 16 =
    ∑ k : Fin 27, lowerUnit entries k 5 * D k * lowerUnit entries k 16 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_5_16_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_5_16_e_oai
