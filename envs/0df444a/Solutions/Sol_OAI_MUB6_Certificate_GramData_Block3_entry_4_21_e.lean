-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_4_21_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:36:31.545596+00:00
-- url     : https://prove2.me/submissions/6f5486c6-0452-4d0b-91a7-6aba9b4fe57b

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_4_21_e_oai : Z 4 21 =
    ∑ k : Fin 27, lowerUnit entries k 4 * D k * lowerUnit entries k 21 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_4_21_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_4_21_e_oai
