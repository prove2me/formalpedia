-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_12_3_11_6
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:36:26.114932+00:00
-- url     : https://prove2.me/submissions/78e67649-6e85-4146-bc87-7602b97441c0

import Mathlib
import Definitions.Def_OAIQ047L000

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0311Batch12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_12_3_11_6_oai : RowCompute.yRowIntegralFast 12 3 11 (RowCompute.rows[6]!) =
    (4877994888074602088933560792038546421903403246042480640000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.computeRow_12_3_11_6_oai := @OAI.Laughlin.Certificate.computeRow_12_3_11_6_oai
