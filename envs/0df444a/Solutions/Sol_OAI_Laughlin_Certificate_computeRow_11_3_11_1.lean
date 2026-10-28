-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_11_3_11_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:27:10.755174+00:00
-- url     : https://prove2.me/submissions/e81df268-cee9-48c0-917c-19e76d9cbb0b

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

theorem computeRow_11_3_11_1_oai : RowCompute.yRowIntegralFast 11 3 11 (RowCompute.rows[1]!) =
    (-126742240405290524556483238589198293423759645285652889600000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.computeRow_11_3_11_1_oai := @OAI.Laughlin.Certificate.computeRow_11_3_11_1_oai
