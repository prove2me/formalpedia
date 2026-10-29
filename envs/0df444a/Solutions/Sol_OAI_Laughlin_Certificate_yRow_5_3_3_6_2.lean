-- Prove2me | solution 2 for OAI.Laughlin.Certificate.yRow_5_3_3_6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:06:47.234991+00:00
-- url     : https://prove2.me/submissions/7333a6d1-809c-4570-a774-b713fabd2dab

import Mathlib
import Definitions.Def_OAIQ047L000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem _root_.solution : yRow 5 3 3 (rows[6]!) = (-175521550402232335797 / 67108864 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end
