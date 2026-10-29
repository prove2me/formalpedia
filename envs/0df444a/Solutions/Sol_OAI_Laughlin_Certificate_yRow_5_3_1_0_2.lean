-- Prove2me | solution 2 for OAI.Laughlin.Certificate.yRow_5_3_1_0
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:07:07.44549+00:00
-- url     : https://prove2.me/submissions/e600189d-51f9-4623-baad-2f0ef1782ffb

import Mathlib
import Definitions.Def_OAIQ047L000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem _root_.solution : yRow 5 3 1 (rows[0]!) = (1227892611554313699 / 32768 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end
