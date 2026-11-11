-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_6_21_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:39:43.139207+00:00
-- url     : https://prove2.me/submissions/255ba058-997c-4768-aa42-f0aea623709d

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_6_21_e_oai : Z 6 21 =
    ∑ k : Fin 27, lowerUnit entries k 6 * D k * lowerUnit entries k 21 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_6_21_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_6_21_e_oai
