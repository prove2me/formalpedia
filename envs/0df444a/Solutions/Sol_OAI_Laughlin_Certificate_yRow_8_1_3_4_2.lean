-- Prove2me | solution 2 for OAI.Laughlin.Certificate.yRow_8_1_3_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:04:22.264448+00:00
-- url     : https://prove2.me/submissions/d00b5c48-4c9e-4582-aca7-7aeb29240a34

import Mathlib
import Definitions.Def_OAIQ047L000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem _root_.solution : yRow 8 1 3 (rows[4]!) = (-441299603451117593115/33554432 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end
