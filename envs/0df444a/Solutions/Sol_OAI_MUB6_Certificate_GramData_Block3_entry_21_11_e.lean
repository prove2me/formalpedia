-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.entry_21_11_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:24:27.147197+00:00
-- url     : https://prove2.me/submissions/6e340452-dde7-4ec9-9edd-a2a4e9bbd2ef

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramData_Block3Check24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_21_11_e_oai : Z 21 11 =
    ∑ k : Fin 27, lowerUnit entries k 21 * D k * lowerUnit entries k 11 := by
  decide +kernel

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.entry_21_11_e_oai := @OAI.MUB6.Certificate.GramData.Block3.entry_21_11_e_oai
