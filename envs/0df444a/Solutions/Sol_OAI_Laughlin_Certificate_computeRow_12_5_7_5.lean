-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_12_5_7_5
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:45:13.687704+00:00
-- url     : https://prove2.me/submissions/6a40d88d-768b-4e13-9780-37dfc69a9bcc

import Mathlib
import Definitions.Def_OAIQ047L000

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0507Batch12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_12_5_7_5_oai : RowCompute.yRowIntegralFast 12 5 7 (RowCompute.rows[5]!) =
    (865670131159668610884971981834212485625140612673044480000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.computeRow_12_5_7_5_oai := @OAI.Laughlin.Certificate.computeRow_12_5_7_5_oai
