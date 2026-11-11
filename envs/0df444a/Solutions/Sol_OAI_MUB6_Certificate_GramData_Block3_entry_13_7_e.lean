-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_13_7_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T08:59:52.408069+00:00
-- url     : https://prove2.me/submissions/de9aad8f-ec06-40ee-8eda-6c459b401223

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

theorem entry_13_7_e_oai : Z 13 7 =
    ∑ k : Fin 27, lowerUnit entries k 13 * D k * lowerUnit entries k 7 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_13_7_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_13_7_e_oai
