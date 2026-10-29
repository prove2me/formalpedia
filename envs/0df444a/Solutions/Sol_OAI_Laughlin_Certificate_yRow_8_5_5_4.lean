-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_8_5_5_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:58:16.155246+00:00
-- url     : https://prove2.me/submissions/ab1faf46-c70d-4803-8492-d3bb06afa38c

import Mathlib
import Definitions.Def_OAIQ047L000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem _root_.solution : yRow 8 5 5 (rows[4]!) = (17756957755544037975/16777216 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end
