-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_11_13_0
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:48:51.938105+00:00
-- url     : https://prove2.me/submissions/b606fa1f-c694-4930-aa71-09fff16783b9

import Mathlib
import Definitions.Def_OAIQ047L000

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow1113Batch13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_13_11_13_0_oai : RowCompute.yRowIntegralFast 13 11 13 (RowCompute.rows[0]!) =
    (4521777551132955453431078454996330441417709705404635676672000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.computeRow_13_11_13_0_oai := @OAI.Laughlin.Certificate.computeRow_13_11_13_0_oai
