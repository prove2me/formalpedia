-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_5_1_5_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T21:05:17.191954+00:00
-- url     : https://prove2.me/submissions/4394833e-27c0-457b-9d93-09f02c66436b

import Mathlib
import Definitions.Def_OAIQ047L000

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_Row05
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem yRow_5_1_5_3_oai : yRow 5 1 5 (rows[3]!) = (-24352127547028721893585 / 234881024 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.yRow_5_1_5_3_oai := @OAI.Laughlin.Certificate.yRow_5_1_5_3_oai
