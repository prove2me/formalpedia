-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_8_3_3_6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:02:20.114171+00:00
-- url     : https://prove2.me/submissions/7f02207c-fa67-48ce-8192-f85122320582

import Mathlib
import Definitions.Def_OAIQ047L000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem _root_.solution : yRow 8 3 3 (rows[6]!) = (-1988696899266245149545/33554432 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end
