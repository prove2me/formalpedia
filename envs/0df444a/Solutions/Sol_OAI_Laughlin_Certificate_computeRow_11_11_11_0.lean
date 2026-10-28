-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_11_11_11_0
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:14:52.698372+00:00
-- url     : https://prove2.me/submissions/1006e639-6180-4315-a84d-a00aef8acbdd

import Mathlib
import Definitions.Def_OAIQ047L000

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow115
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_11_11_11_0_oai : RowCompute.yRowIntegralFast 11 11 11 (RowCompute.rows[0]!) =
    (1459948519991364483667067515869070225225026658118582403072000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.computeRow_11_11_11_0_oai := @OAI.Laughlin.Certificate.computeRow_11_11_11_0_oai
