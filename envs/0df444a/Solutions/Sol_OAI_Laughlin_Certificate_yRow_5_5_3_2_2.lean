-- Prove2me | solution 2 for OAI.Laughlin.Certificate.yRow_5_5_3_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:04:56.770933+00:00
-- url     : https://prove2.me/submissions/7b704f55-0bf8-4b72-846c-8478e00c40a4

import Mathlib
import Definitions.Def_OAIQ047L000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem _root_.solution : yRow 5 5 3 (rows[2]!) = (4154519314999427044985 / 469762048 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end
