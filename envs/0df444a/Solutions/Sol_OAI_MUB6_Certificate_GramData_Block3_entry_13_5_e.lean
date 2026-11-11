-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_13_5_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T08:59:50.236554+00:00
-- url     : https://prove2.me/submissions/540f3821-9b73-4f4e-9814-4506482ec69f

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

theorem entry_13_5_e_oai : Z 13 5 =
    ∑ k : Fin 27, lowerUnit entries k 13 * D k * lowerUnit entries k 5 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_13_5_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_13_5_e_oai
