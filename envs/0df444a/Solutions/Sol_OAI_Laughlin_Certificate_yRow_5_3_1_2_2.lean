-- Prove2me | solution 2 for OAI.Laughlin.Certificate.yRow_5_3_1_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:07:04.559238+00:00
-- url     : https://prove2.me/submissions/4af0a871-14f5-438c-9810-29d848eef393

import Mathlib
import Definitions.Def_OAIQ047L000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem _root_.solution : yRow 5 3 1 (rows[2]!) = (3609794378028611869977 / 1879048192 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end
