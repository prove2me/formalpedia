-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_8_3_5_6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:58:33.680982+00:00
-- url     : https://prove2.me/submissions/c768e187-fb90-45eb-b73c-560297892d97

import Mathlib
import Definitions.Def_OAIQ047L000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem _root_.solution : yRow 8 3 5 (rows[6]!) = (-74303915387983228845/2097152 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end
