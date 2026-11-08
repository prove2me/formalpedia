-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_15_21_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T20:38:56.468202+00:00
-- url     : https://prove2.me/submissions/dc88efbf-9f6a-47a5-a70b-615bd227ae2e

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_15_21_e_oai : Z 15 21 =
    ∑ k : Fin 27, lowerUnit entries k 15 * D k * lowerUnit entries k 21 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_15_21_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_15_21_e_oai
