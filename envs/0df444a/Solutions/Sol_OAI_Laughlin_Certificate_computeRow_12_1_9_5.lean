-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_12_1_9_5
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:33:28.431419+00:00
-- url     : https://prove2.me/submissions/2b0e530d-7046-470b-9816-0311f19848f5

import Mathlib
import Definitions.Def_OAIQ047L000

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0109Batch12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_12_1_9_5_oai : RowCompute.yRowIntegralFast 12 1 9 (RowCompute.rows[5]!) =
    (64611594140891400007864625718557689126762003439133130752000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.computeRow_12_1_9_5_oai := @OAI.Laughlin.Certificate.computeRow_12_1_9_5_oai
