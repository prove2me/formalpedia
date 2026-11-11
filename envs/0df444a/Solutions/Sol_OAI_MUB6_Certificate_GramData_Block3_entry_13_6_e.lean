-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_13_6_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T08:59:51.223061+00:00
-- url     : https://prove2.me/submissions/2165974b-bd64-4964-a33e-6e86d95c7833

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

theorem entry_13_6_e_oai : Z 13 6 =
    ∑ k : Fin 27, lowerUnit entries k 13 * D k * lowerUnit entries k 6 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_13_6_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_13_6_e_oai
