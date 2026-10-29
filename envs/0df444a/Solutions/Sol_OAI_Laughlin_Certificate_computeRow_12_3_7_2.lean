-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_12_3_7_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:40:51.854995+00:00
-- url     : https://prove2.me/submissions/1174fe9c-5bbb-4a5a-8348-67d362a5d1bf

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

theorem computeRow_12_3_7_2_oai : RowCompute.yRowIntegralFast 12 3 7 (RowCompute.rows[2]!) =
    (7784022533757794511685165325925345472845446908288696320000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.computeRow_12_3_7_2_oai := @OAI.Laughlin.Certificate.computeRow_12_3_7_2_oai
