-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_10_7_7_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T19:49:50.350856+00:00
-- url     : https://prove2.me/submissions/b0c298d7-d25c-4cd8-91e0-a242cdd09fff

import Mathlib
import Definitions.Def_OAIQ047L000

namespace OAI
namespace Laughlin.Certificate


theorem _root_.solution : RowCompute.yRowIntegralFast 10 7 7 (RowCompute.rows[4]!) =
    (-39057344256105315958191321295757808084261599215563571200000 : ℤ) := by
  decide +kernel
end Laughlin.Certificate
end OAI
