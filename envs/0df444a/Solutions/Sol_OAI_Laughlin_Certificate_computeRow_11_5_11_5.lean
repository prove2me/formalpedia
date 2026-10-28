-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_11_5_11_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T19:11:32.601892+00:00
-- url     : https://prove2.me/submissions/d0fd86ae-3789-4122-a8a8-eaaf80fbe12e

import Mathlib
import Definitions.Def_OAIQ047L000

namespace OAI
namespace Laughlin.Certificate


theorem _root_.solution : RowCompute.yRowIntegralFast 11 5 11 (RowCompute.rows[5]!) =
    (-1132177804292779484603226894742950747954830127113699328000000 : ℤ) := by
  decide +kernel
end Laughlin.Certificate
end OAI
