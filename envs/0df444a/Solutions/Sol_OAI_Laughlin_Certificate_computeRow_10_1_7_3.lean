-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_10_1_7_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:12:32.30777+00:00
-- url     : https://prove2.me/submissions/cf71476f-b1cb-46c1-aed6-fb82e62f29c9

import Mathlib
import Definitions.Def_OAIQ047L000

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_10_1_7_3_oai : RowCompute.yRowIntegralFast 10 1 7 (RowCompute.rows[3]!) =
    (2575824189323123164128005605276043836778377513447037337600000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.computeRow_10_1_7_3_oai := @OAI.Laughlin.Certificate.computeRow_10_1_7_3_oai
