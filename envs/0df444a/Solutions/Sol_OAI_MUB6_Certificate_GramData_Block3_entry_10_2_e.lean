-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_10_2_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T20:34:18.804923+00:00
-- url     : https://prove2.me/submissions/11153229-266d-432e-aa21-cb8330107fec

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_10_2_e_oai : Z 10 2 =
    ∑ k : Fin 27, lowerUnit entries k 10 * D k * lowerUnit entries k 2 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_10_2_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_10_2_e_oai
