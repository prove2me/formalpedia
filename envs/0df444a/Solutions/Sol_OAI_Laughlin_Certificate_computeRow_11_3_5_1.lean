-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_11_3_5_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T19:15:46.855217+00:00
-- url     : https://prove2.me/submissions/82998a23-d94b-4430-8381-3871d0d490e8

import Mathlib
import Definitions.Def_OAIQ047L000

namespace OAI
namespace Laughlin.Certificate


theorem _root_.solution : RowCompute.yRowIntegralFast 11 3 5 (RowCompute.rows[1]!) =
    (2177629232122608185133948894840466665565613526614016000000 : ℤ) := by
  decide +kernel
end Laughlin.Certificate
end OAI
