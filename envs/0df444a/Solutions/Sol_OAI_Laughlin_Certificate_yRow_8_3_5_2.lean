-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_8_3_5_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:02:23.578757+00:00
-- url     : https://prove2.me/submissions/0fa37cd5-71ba-4c94-a09d-7ce024626f3e

import Mathlib
import Definitions.Def_OAIQ047L000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem _root_.solution : yRow 8 3 5 (rows[2]!) = (2761275840379361416995/4194304 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end
