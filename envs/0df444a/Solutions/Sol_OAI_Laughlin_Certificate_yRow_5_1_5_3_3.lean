-- Prove2me | solution 3 for OAI.Laughlin.Certificate.yRow_5_1_5_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:08:54.408613+00:00
-- url     : https://prove2.me/submissions/8b97e352-1c10-4749-a600-d8f555506950

import Mathlib
import Definitions.Def_OAIQ047L000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem _root_.solution : yRow 5 1 5 (rows[3]!) = (-24352127547028721893585 / 234881024 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end
