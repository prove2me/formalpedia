-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_5_1_1_5
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:57:12.406453+00:00
-- url     : https://prove2.me/submissions/2ab8879d-f32d-412f-9e1b-ff9feb2e0a1e

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

theorem yRow_5_1_1_5_oai : yRow 5 1 1 (rows[5]!) = (10589763940221275062345 / 536870912 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.yRow_5_1_1_5_oai := @OAI.Laughlin.Certificate.yRow_5_1_1_5_oai
