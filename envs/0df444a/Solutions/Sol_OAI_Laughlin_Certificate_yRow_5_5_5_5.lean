-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_5_5_5_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:04:42.38356+00:00
-- url     : https://prove2.me/submissions/2ce3955c-0679-4af7-88a0-7c33aaa5b18c

import Mathlib
import Definitions.Def_OAIQ047L000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem _root_.solution : yRow 5 5 5 (rows[5]!) = (52813174350218993123795 / 536870912 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end
