-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_11_3_11_5
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:27:33.554018+00:00
-- url     : https://prove2.me/submissions/b4175045-c1f0-453b-814b-fd2758ad9bb3

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

theorem computeRow_11_3_11_5_oai : RowCompute.yRowIntegralFast 11 3 11 (RowCompute.rows[5]!) =
    (17729530118954365262841828307280161229016394297937756160000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.computeRow_11_3_11_5_oai := @OAI.Laughlin.Certificate.computeRow_11_3_11_5_oai
