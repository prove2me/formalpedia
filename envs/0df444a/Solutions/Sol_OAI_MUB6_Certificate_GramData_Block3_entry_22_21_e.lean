-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_22_21_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T10:13:17.547826+00:00
-- url     : https://prove2.me/submissions/7f72469e-5f50-4cbf-8270-4600e0cc6913

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_22_21_e_oai : Z 22 21 =
    ∑ k : Fin 27, lowerUnit entries k 22 * D k * lowerUnit entries k 21 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_22_21_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_22_21_e_oai
