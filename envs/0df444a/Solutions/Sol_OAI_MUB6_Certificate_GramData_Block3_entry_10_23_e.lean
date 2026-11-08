-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_10_23_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T20:34:33.955192+00:00
-- url     : https://prove2.me/submissions/9db3c6f4-21b7-4271-870d-94330c21d60e

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

theorem entry_10_23_e_oai : Z 10 23 =
    ∑ k : Fin 27, lowerUnit entries k 10 * D k * lowerUnit entries k 23 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_10_23_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_10_23_e_oai
