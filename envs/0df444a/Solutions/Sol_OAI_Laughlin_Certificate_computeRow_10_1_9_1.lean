-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_10_1_9_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:13:16.568165+00:00
-- url     : https://prove2.me/submissions/94118602-c333-478f-958f-352534845e3a

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

theorem computeRow_10_1_9_1_oai : RowCompute.yRowIntegralFast 10 1 9 (RowCompute.rows[1]!) =
    (-12889460886454364993255275656452903527812102494984601600000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.computeRow_10_1_9_1_oai := @OAI.Laughlin.Certificate.computeRow_10_1_9_1_oai
