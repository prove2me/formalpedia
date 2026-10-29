-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_5_5_3_0
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:04:59.469834+00:00
-- url     : https://prove2.me/submissions/28c6ed67-347b-4b00-a106-49da8ea1e193

import Mathlib
import Definitions.Def_OAIQ047L000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem _root_.solution : yRow 5 5 3 (rows[0]!) = (2088880360412782875 / 8192 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end
