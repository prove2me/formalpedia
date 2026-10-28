-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_12_1_7_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:30:33.080186+00:00
-- url     : https://prove2.me/submissions/25ceee3b-6e8a-40bb-918a-7c69f8350b28

import Mathlib
import Definitions.Def_OAIQ047L000

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0107Batch12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_12_1_7_4_oai : RowCompute.yRowIntegralFast 12 1 7 (RowCompute.rows[4]!) =
    (-2849415289265387837434248874016901134675220062332256256000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.computeRow_12_1_7_4_oai := @OAI.Laughlin.Certificate.computeRow_12_1_7_4_oai
