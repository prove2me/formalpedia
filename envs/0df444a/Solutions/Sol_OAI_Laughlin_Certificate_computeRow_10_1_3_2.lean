-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_10_1_3_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:10:17.867276+00:00
-- url     : https://prove2.me/submissions/8eaf3397-ef78-4410-9688-ba15035bf6ce

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

theorem computeRow_10_1_3_2_oai : RowCompute.yRowIntegralFast 10 1 3 (RowCompute.rows[2]!) =
    (3047114270145231300254030795779897789688217886779663974400000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.computeRow_10_1_3_2_oai := @OAI.Laughlin.Certificate.computeRow_10_1_3_2_oai
