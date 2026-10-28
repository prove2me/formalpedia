-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_10_7_9_0
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T19:49:47.332917+00:00
-- url     : https://prove2.me/submissions/7caa3dbd-d49d-4987-a089-ab52e44731a0

import Mathlib
import Definitions.Def_OAIQ047L000

namespace OAI
namespace Laughlin.Certificate


theorem _root_.solution : RowCompute.yRowIntegralFast 10 7 9 (RowCompute.rows[0]!) =
    (7225248175512217488716066456062230481089753653573792563200000 : ℤ) := by
  decide +kernel
end Laughlin.Certificate
end OAI
