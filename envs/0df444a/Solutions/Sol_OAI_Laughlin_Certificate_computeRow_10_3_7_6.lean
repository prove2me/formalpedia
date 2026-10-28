-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_10_3_7_6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:11:03.499848+00:00
-- url     : https://prove2.me/submissions/e90dd67f-0124-4f24-bfc6-356a8133bf16

import Mathlib
import Definitions.Def_OAIQ047L000

namespace OAI
namespace Laughlin.Certificate


theorem _root_.solution : RowCompute.yRowIntegralFast 10 3 7 (RowCompute.rows[6]!) =
    (-27598052737685595644452936414890275236776185186746368000000 : ℤ) := by
  decide +kernel
end Laughlin.Certificate
end OAI
