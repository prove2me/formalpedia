-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_11_1_11_5
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:16:47.101133+00:00
-- url     : https://prove2.me/submissions/f4299b06-540c-4d2c-9ef8-65226bf54d6c

import Mathlib
import Definitions.Def_OAIQ047L000

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow112
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_11_1_11_5_oai : RowCompute.yRowIntegralFast 11 1 11 (RowCompute.rows[5]!) =
    (-26337989445769093433243047633684203007243476521906601984000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.computeRow_11_1_11_5_oai := @OAI.Laughlin.Certificate.computeRow_11_1_11_5_oai
