-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_11_7_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T08:55:55.126184+00:00
-- url     : https://prove2.me/submissions/1ccd0ba6-f8a9-4b94-a261-b6cc05c044e9

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

theorem entry_11_7_e_oai : Z 11 7 =
    ∑ k : Fin 27, lowerUnit entries k 11 * D k * lowerUnit entries k 7 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_11_7_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_11_7_e_oai
