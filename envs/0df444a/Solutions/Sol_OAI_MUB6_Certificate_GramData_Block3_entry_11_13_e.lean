-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_11_13_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T20:36:10.191693+00:00
-- url     : https://prove2.me/submissions/8623988e-6fc6-4d69-a29c-c1aa24aa7d2c

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

theorem entry_11_13_e_oai : Z 11 13 =
    ∑ k : Fin 27, lowerUnit entries k 11 * D k * lowerUnit entries k 13 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_11_13_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_11_13_e_oai
