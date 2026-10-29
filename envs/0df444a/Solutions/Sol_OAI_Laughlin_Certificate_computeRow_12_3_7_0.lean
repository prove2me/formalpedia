-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_12_3_7_0
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:39:24.967292+00:00
-- url     : https://prove2.me/submissions/12d9c142-8214-4ec5-8b7a-0c19f826c0e9

import Mathlib
import Definitions.Def_OAIQ047L000

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0307Batch12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_12_3_7_0_oai : RowCompute.yRowIntegralFast 12 3 7 (RowCompute.rows[0]!) =
    (-25875316937120714040935923332472621826321982773482487808000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.computeRow_12_3_7_0_oai := @OAI.Laughlin.Certificate.computeRow_12_3_7_0_oai
