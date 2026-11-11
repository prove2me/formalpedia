-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_11_6_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T08:55:54.122059+00:00
-- url     : https://prove2.me/submissions/e2549780-3bd2-4445-ae67-b426a8bf12c0

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_11_6_e_oai : Z 11 6 =
    ∑ k : Fin 27, lowerUnit entries k 11 * D k * lowerUnit entries k 6 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_11_6_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_11_6_e_oai
