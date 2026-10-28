-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_10_1_3_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:10:40.344638+00:00
-- url     : https://prove2.me/submissions/e7b92ec5-1827-4326-ab5f-8113e3c115cb

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

theorem computeRow_10_1_3_4_oai : RowCompute.yRowIntegralFast 10 1 3 (RowCompute.rows[4]!) =
    (10831745845708605030561628151940631317774179790697267200000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.computeRow_10_1_3_4_oai := @OAI.Laughlin.Certificate.computeRow_10_1_3_4_oai
