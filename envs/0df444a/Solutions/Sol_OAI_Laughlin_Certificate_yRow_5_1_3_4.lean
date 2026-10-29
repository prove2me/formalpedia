-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_5_1_3_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T21:02:22.77893+00:00
-- url     : https://prove2.me/submissions/0698c2e7-c98f-44b1-a821-9812906c9348

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

theorem yRow_5_1_3_4_oai : yRow 5 1 3 (rows[4]!) = (973139460225276068975 / 939524096 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.yRow_5_1_3_4_oai := @OAI.Laughlin.Certificate.yRow_5_1_3_4_oai
