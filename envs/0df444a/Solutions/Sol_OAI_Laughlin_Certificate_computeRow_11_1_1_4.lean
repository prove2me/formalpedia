-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_11_1_1_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:17:54.388786+00:00
-- url     : https://prove2.me/submissions/ca3e8acd-7bc1-4a71-895b-4bdd455cdb9b

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

theorem computeRow_11_1_1_4_oai : RowCompute.yRowIntegralFast 11 1 1 (RowCompute.rows[4]!) =
    (-902807179373510648718861695766049025556764986649346048000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.computeRow_11_1_1_4_oai := @OAI.Laughlin.Certificate.computeRow_11_1_1_4_oai
