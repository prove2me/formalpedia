-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_7_17_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:42:07.678555+00:00
-- url     : https://prove2.me/submissions/6bc76519-5a03-479d-bfd6-c219824304f7

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_7_17_e_oai : Z 7 17 =
    ∑ k : Fin 27, lowerUnit entries k 7 * D k * lowerUnit entries k 17 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_7_17_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_7_17_e_oai
