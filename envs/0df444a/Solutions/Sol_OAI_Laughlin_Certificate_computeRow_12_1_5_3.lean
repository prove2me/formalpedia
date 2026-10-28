-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_12_1_5_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:30:08.718131+00:00
-- url     : https://prove2.me/submissions/b4994134-a6d5-43ef-864f-1e3298a5abea

import Mathlib
import Definitions.Def_OAIQ047L000

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow0105Batch12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_12_1_5_3_oai : RowCompute.yRowIntegralFast 12 1 5 (RowCompute.rows[3]!) =
    (-33387227084822278248292418260490663958417943240686698496000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.computeRow_12_1_5_3_oai := @OAI.Laughlin.Certificate.computeRow_12_1_5_3_oai
