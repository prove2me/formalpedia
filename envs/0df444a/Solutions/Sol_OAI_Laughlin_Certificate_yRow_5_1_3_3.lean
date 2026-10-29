-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_5_1_3_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T21:02:21.679783+00:00
-- url     : https://prove2.me/submissions/aad11ada-dadd-4f6b-ab57-15779f4161be

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

theorem yRow_5_1_3_3_oai : yRow 5 1 3 (rows[3]!) = (15972179718835785494373 / 469762048 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.yRow_5_1_3_3_oai := @OAI.Laughlin.Certificate.yRow_5_1_3_3_oai
