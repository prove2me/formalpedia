-- Prove2me | solution 2 for OAI.Laughlin.Certificate.yRow_8_1_1_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:04:31.017375+00:00
-- url     : https://prove2.me/submissions/ac3a0716-2af8-4efe-9723-e91611118b88

import Mathlib
import Definitions.Def_OAIQ047L000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem _root_.solution : yRow 8 1 1 (rows[5]!) = (-347441421785295611479515/67108864 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end
