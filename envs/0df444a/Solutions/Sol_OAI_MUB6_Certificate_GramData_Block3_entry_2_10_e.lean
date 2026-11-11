-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_2_10_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:22:15.0673+00:00
-- url     : https://prove2.me/submissions/cb2b31df-8360-44db-878f-40e2fb9779ed

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_2_10_e_oai : Z 2 10 =
    ∑ k : Fin 27, lowerUnit entries k 2 * D k * lowerUnit entries k 10 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_2_10_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_2_10_e_oai
