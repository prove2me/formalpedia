-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_5_19_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T20:41:50.270762+00:00
-- url     : https://prove2.me/submissions/bfcb7431-de68-48c4-85b9-026681899d9f

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

theorem entry_5_19_e_oai : Z 5 19 =
    ∑ k : Fin 27, lowerUnit entries k 5 * D k * lowerUnit entries k 19 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_5_19_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_5_19_e_oai
