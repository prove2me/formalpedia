-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_8_1_3_0
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:04:24.995907+00:00
-- url     : https://prove2.me/submissions/6e677eab-f06d-4f2b-83d4-c1efae893c03

import Mathlib
import Definitions.Def_OAIQ047L000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem _root_.solution : yRow 8 1 3 (rows[0]!) = (-11387494346113586295/8192 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end
