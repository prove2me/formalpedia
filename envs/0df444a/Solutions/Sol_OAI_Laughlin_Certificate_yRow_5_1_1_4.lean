-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_5_1_1_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:57:11.433778+00:00
-- url     : https://prove2.me/submissions/ae1b3da8-18a3-4e95-bd9a-8b3039712c16

import Mathlib
import Definitions.Def_OAIQ047L000

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_Row05
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem yRow_5_1_1_4_oai : yRow 5 1 1 (rows[4]!) = (307361222967220883631 / 67108864 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.yRow_5_1_1_4_oai := @OAI.Laughlin.Certificate.yRow_5_1_1_4_oai
