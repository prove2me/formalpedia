-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_21_2_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:23:48.118798+00:00
-- url     : https://prove2.me/submissions/4c1f580d-bc1c-497d-819e-0fcc5feca98d

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_21_2_e_oai : Z 21 2 =
    ∑ k : Fin 27, lowerUnit entries k 21 * D k * lowerUnit entries k 2 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_21_2_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_21_2_e_oai
