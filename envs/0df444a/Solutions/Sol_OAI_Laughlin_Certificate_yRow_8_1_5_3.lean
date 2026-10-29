-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_8_1_5_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:02:49.264706+00:00
-- url     : https://prove2.me/submissions/0fa1864e-2939-4fb4-873f-08e14e2beed9

import Mathlib
import Definitions.Def_OAIQ047L000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem _root_.solution : yRow 8 1 5 (rows[3]!) = (13068275739016009424895/16777216 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end
