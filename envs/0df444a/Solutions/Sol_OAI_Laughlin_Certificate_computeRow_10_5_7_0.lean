-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_10_5_7_0
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T19:50:09.316058+00:00
-- url     : https://prove2.me/submissions/fbe29f31-8673-4d68-a66c-530964646a4f

import Mathlib
import Definitions.Def_OAIQ047L000

namespace OAI
namespace Laughlin.Certificate


theorem _root_.solution : RowCompute.yRowIntegralFast 10 5 7 (RowCompute.rows[0]!) =
    (1068075642404633103309673045448614116469774732832538624000000 : ℤ) := by
  decide +kernel
end Laughlin.Certificate
end OAI
