-- Prove2me | solution 2 for OAI.Laughlin.Certificate.yRow_5_3_5_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:06:50.287269+00:00
-- url     : https://prove2.me/submissions/e22f8c52-3c95-4bf9-994b-9c55c25f9cd4

import Mathlib
import Definitions.Def_OAIQ047L000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem _root_.solution : yRow 5 3 5 (rows[1]!) = (9078017688703880489 / 117440512 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end
