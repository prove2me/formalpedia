-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_11_1_7_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:23:09.421891+00:00
-- url     : https://prove2.me/submissions/35a35cd0-d61a-417e-acbe-89aa3d9d86e6

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

theorem computeRow_11_1_7_4_oai : RowCompute.yRowIntegralFast 11 1 7 (RowCompute.rows[4]!) =
    (360054190156783050878552131535741760706547398138134528000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.computeRow_11_1_7_4_oai := @OAI.Laughlin.Certificate.computeRow_11_1_7_4_oai
