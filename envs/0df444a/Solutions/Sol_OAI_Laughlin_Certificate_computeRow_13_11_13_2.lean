-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_11_13_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:48:53.182132+00:00
-- url     : https://prove2.me/submissions/048fd70b-eefc-451d-8b85-a241e73639ba

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

theorem computeRow_13_11_13_2_oai : RowCompute.yRowIntegralFast 13 11 13 (RowCompute.rows[2]!) =
    (-15855944916600974309347236550626135160731512422348250677248000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.computeRow_13_11_13_2_oai := @OAI.Laughlin.Certificate.computeRow_13_11_13_2_oai
