-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_8_5_7_0
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:58:06.712519+00:00
-- url     : https://prove2.me/submissions/3314918e-a47e-437e-86cb-8a684482ed3f

import Mathlib
import Definitions.Def_OAIQ047L000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem _root_.solution : yRow 8 5 7 (rows[0]!) = (-2272256943023826045/256 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end
