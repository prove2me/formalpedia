-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_12_1_1_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T19:03:14.414038+00:00
-- url     : https://prove2.me/submissions/39d60611-1cf9-4f2d-84c6-04f2c90350c8

import Mathlib
import Definitions.Def_OAIQ047L000

namespace OAI
namespace Laughlin.Certificate


theorem _root_.solution : RowCompute.yRowIntegralFast 12 1 1 (RowCompute.rows[4]!) =
    (-165298721136013806051235802312235009641326368710782353408000000 : ℤ) := by
  decide +kernel
end Laughlin.Certificate
end OAI
