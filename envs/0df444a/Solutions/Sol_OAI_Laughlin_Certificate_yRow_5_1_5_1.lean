-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_5_1_5_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T21:04:12.262687+00:00
-- url     : https://prove2.me/submissions/285d9d19-e0ac-4941-ab35-b61ae79636eb

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

theorem yRow_5_1_5_1_oai : yRow 5 1 5 (rows[1]!) = (33354143675585625297 / 234881024 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.yRow_5_1_5_1_oai := @OAI.Laughlin.Certificate.yRow_5_1_5_1_oai
