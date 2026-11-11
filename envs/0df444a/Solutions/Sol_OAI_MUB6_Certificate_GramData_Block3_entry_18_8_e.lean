-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_18_8_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:10:13.558414+00:00
-- url     : https://prove2.me/submissions/86a1099b-0f83-4697-a25c-f61bd77c1068

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_18_8_e_oai : Z 18 8 =
    ∑ k : Fin 27, lowerUnit entries k 18 * D k * lowerUnit entries k 8 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_18_8_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_18_8_e_oai
