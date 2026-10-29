-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_5_1_3_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:59:49.188838+00:00
-- url     : https://prove2.me/submissions/1459e7bf-26a4-48f7-aabc-78b8c2fbcdf9

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

theorem yRow_5_1_3_1_oai : yRow 5 1 3 (rows[1]!) = (-40217208208139155215 / 469762048 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.yRow_5_1_3_1_oai := @OAI.Laughlin.Certificate.yRow_5_1_3_1_oai
