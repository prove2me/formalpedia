-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_11_3_11_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:27:32.62898+00:00
-- url     : https://prove2.me/submissions/6710148e-1032-41cf-ab18-d94ebdcf2b6b

import Mathlib
import Definitions.Def_OAIQ047L000

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow113
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_11_3_11_3_oai : RowCompute.yRowIntegralFast 11 3 11 (RowCompute.rows[3]!) =
    (11771066955034366064885417986755534179015093098930765824000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.computeRow_11_3_11_3_oai := @OAI.Laughlin.Certificate.computeRow_11_3_11_3_oai
