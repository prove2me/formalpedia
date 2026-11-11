-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_4_3_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:37:08.831422+00:00
-- url     : https://prove2.me/submissions/fb6efc68-6cda-4611-b46e-3eb65b968411

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_4_3_e_oai : Z 4 3 =
    ∑ k : Fin 27, lowerUnit entries k 4 * D k * lowerUnit entries k 3 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_4_3_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_4_3_e_oai
