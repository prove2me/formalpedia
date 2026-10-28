-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_11_1_5_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:20:10.798854+00:00
-- url     : https://prove2.me/submissions/a86040bd-3cf2-4b61-9fe7-9216ec9909b0

import Mathlib
import Definitions.Def_OAIQ047L000

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_11_1_5_1_oai : RowCompute.yRowIntegralFast 11 1 5 (RowCompute.rows[1]!) =
    (-30053457338581216450474940629405845229378089951166464000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.computeRow_11_1_5_1_oai := @OAI.Laughlin.Certificate.computeRow_11_1_5_1_oai
