-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_11_1_1_6
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:18:17.28858+00:00
-- url     : https://prove2.me/submissions/2993b7ac-e950-4005-b482-dadbeebd450d

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

theorem computeRow_11_1_1_6_oai : RowCompute.yRowIntegralFast 11 1 1 (RowCompute.rows[6]!) =
    (-7596659047863245891354033400517136591644783148141641728000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.computeRow_11_1_1_6_oai := @OAI.Laughlin.Certificate.computeRow_11_1_1_6_oai
