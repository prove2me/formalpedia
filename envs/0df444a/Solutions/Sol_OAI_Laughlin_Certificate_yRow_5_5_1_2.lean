-- Prove2me | solution 1 for OAI.Laughlin.Certificate.yRow_5_5_1_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:05:02.369002+00:00
-- url     : https://prove2.me/submissions/7ba53405-2fda-4616-b3eb-0297e0fb1523

import Mathlib
import Definitions.Def_OAIQ047L000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem _root_.solution : yRow 5 5 1 (rows[2]!) = (-39698825671225989422295 / 939524096 : ℚ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end
