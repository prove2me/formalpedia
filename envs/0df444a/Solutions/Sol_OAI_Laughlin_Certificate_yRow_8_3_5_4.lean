-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_8_3_5_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:58:37.597991+00:00
-- url     : https://prove2.me/submissions/fbc92036-994f-46c3-9d07-ad5263ad2d3e

import Mathlib
import Definitions.Def_OAIQ047L000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem _root_.solution : yRow 8 3 5 (rows[4]!) = (2911950561638159921355/33554432 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end
