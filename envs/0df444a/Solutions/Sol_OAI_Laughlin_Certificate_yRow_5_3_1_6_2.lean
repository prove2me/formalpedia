-- Prove2me | solution 2 for OAI.Laughlin.Certificate.yRow_5_3_1_6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:06:58.654152+00:00
-- url     : https://prove2.me/submissions/159d6caf-3ae0-4793-8277-3d90f3b0a1e1

import Mathlib
import Definitions.Def_OAIQ047L000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem _root_.solution : yRow 5 3 1 (rows[6]!) = (-26195139147988314471 / 8388608 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end
