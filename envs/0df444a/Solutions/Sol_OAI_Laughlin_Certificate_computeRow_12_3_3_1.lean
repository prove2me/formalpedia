-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_12_3_3_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:36:27.342115+00:00
-- url     : https://prove2.me/submissions/ba40ce1a-1287-4932-beda-c2f1dcd398f5

import Mathlib
import Definitions.Def_OAIQ047L000

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0303Batch12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_12_3_3_1_oai : RowCompute.yRowIntegralFast 12 3 3 (RowCompute.rows[1]!) =
    (-37891520281238942633413704942445960254385802878491033600000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.computeRow_12_3_3_1_oai := @OAI.Laughlin.Certificate.computeRow_12_3_3_1_oai
