-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_12_3_9_5
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:43:02.854226+00:00
-- url     : https://prove2.me/submissions/5ab9f6a6-b420-4748-9b66-2105a65246f4

import Mathlib
import Definitions.Def_OAIQ047L000

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0309Batch12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_12_3_9_5_oai : RowCompute.yRowIntegralFast 12 3 9 (RowCompute.rows[5]!) =
    (-11437795200136124138107274305687368386506072534821529190400000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.computeRow_12_3_9_5_oai := @OAI.Laughlin.Certificate.computeRow_12_3_9_5_oai
