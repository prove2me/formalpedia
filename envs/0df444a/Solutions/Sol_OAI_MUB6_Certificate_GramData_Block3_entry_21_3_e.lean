-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_21_3_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:25:51.602534+00:00
-- url     : https://prove2.me/submissions/aa6dfaa2-b5aa-47bc-8003-5e790f9e0e8e

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

theorem entry_21_3_e_oai : Z 21 3 =
    ∑ k : Fin 27, lowerUnit entries k 21 * D k * lowerUnit entries k 3 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_21_3_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_21_3_e_oai
