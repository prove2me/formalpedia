-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_11_1_3_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:18:41.064351+00:00
-- url     : https://prove2.me/submissions/13676c89-8f59-44b0-bb2b-8390d629bf83

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

theorem computeRow_11_1_3_2_oai : RowCompute.yRowIntegralFast 11 1 3 (RowCompute.rows[2]!) =
    (46321427748934307911284639067506368688424353074270699520000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.computeRow_11_1_3_2_oai := @OAI.Laughlin.Certificate.computeRow_11_1_3_2_oai
