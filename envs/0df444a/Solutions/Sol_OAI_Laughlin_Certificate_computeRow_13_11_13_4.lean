-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_13_11_13_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:48:54.260676+00:00
-- url     : https://prove2.me/submissions/cb35fed8-63f3-447d-bd0b-7caa8617e202

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

theorem computeRow_13_11_13_4_oai : RowCompute.yRowIntegralFast 13 11 13 (RowCompute.rows[4]!) =
    (753927761098496303820746753312129856719479149477859688448000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.computeRow_13_11_13_4_oai := @OAI.Laughlin.Certificate.computeRow_13_11_13_4_oai
