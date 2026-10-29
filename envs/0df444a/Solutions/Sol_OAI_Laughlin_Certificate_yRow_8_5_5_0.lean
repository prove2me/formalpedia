-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_8_5_5_0
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:58:19.62104+00:00
-- url     : https://prove2.me/submissions/e45d38e2-6f19-4f15-b344-e9edd32402aa

import Mathlib
import Definitions.Def_OAIQ047L000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem _root_.solution : yRow 8 5 5 (rows[0]!) = (-2191463802492555735/512 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end
