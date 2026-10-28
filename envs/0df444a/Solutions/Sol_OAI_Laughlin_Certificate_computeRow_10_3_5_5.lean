-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_10_3_5_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:11:22.839196+00:00
-- url     : https://prove2.me/submissions/0adefd65-798e-468c-89b0-bd8b59af3a39

import Mathlib
import Definitions.Def_OAIQ047L000

namespace OAI
namespace Laughlin.Certificate


theorem _root_.solution : RowCompute.yRowIntegralFast 10 3 5 (RowCompute.rows[5]!) =
    (30906469836729970035282498304064865040300729316671488000000 : ℤ) := by
  decide +kernel
end Laughlin.Certificate
end OAI
