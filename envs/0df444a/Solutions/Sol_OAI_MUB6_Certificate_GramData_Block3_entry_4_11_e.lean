-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_4_11_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:34:44.031094+00:00
-- url     : https://prove2.me/submissions/18bf8032-5334-4661-8c1e-14c6c24f4100

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

theorem entry_4_11_e_oai : Z 4 11 =
    ∑ k : Fin 27, lowerUnit entries k 4 * D k * lowerUnit entries k 11 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_4_11_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_4_11_e_oai
