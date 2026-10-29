-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_5_1_1_0
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:54:37.891563+00:00
-- url     : https://prove2.me/submissions/a24b95c1-3824-4ce4-953b-175c1ec302df

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

theorem yRow_5_1_1_0_oai : yRow 5 1 1 (rows[0]!) = (288217185514048371 / 32768 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.yRow_5_1_1_0_oai := @OAI.Laughlin.Certificate.yRow_5_1_1_0_oai
