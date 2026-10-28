-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_12_1_3_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T19:02:58.918409+00:00
-- url     : https://prove2.me/submissions/f34f37b8-caf5-4a06-a098-39434dda6a30

import Mathlib
import Definitions.Def_OAIQ047L000

namespace OAI
namespace Laughlin.Certificate


theorem _root_.solution : RowCompute.yRowIntegralFast 12 1 3 (RowCompute.rows[5]!) =
    (15695184593451429576872589563489060401589685500422127616000000 : ℤ) := by
  decide +kernel
end Laughlin.Certificate
end OAI
