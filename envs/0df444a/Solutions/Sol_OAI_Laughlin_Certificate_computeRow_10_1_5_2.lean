-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_10_1_5_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:12:08.991644+00:00
-- url     : https://prove2.me/submissions/284ef216-3c1a-4f92-8b68-ddc487721f53

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

theorem computeRow_10_1_5_2_oai : RowCompute.yRowIntegralFast 10 1 5 (RowCompute.rows[2]!) =
    (-3137716928338913299049302516211816564056239387439005696000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.computeRow_10_1_5_2_oai := @OAI.Laughlin.Certificate.computeRow_10_1_5_2_oai
