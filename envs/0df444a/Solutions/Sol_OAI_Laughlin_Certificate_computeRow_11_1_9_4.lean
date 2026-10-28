-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_11_1_9_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:25:43.691341+00:00
-- url     : https://prove2.me/submissions/eb24de59-f4db-4d8f-96cb-11bde673553e

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

theorem computeRow_11_1_9_4_oai : RowCompute.yRowIntegralFast 11 1 9 (RowCompute.rows[4]!) =
    (1741796590967689308679558667982808992287706163137478656000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.computeRow_11_1_9_4_oai := @OAI.Laughlin.Certificate.computeRow_11_1_9_4_oai
