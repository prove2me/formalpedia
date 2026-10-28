-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_11_3_9_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T19:15:13.069951+00:00
-- url     : https://prove2.me/submissions/5e9b082e-be07-497b-aa4a-9ac1882fedd4

import Mathlib
import Definitions.Def_OAIQ047L000

namespace OAI
namespace Laughlin.Certificate


theorem _root_.solution : RowCompute.yRowIntegralFast 11 3 9 (RowCompute.rows[4]!) =
    (-356359027678216428465772118219438346644822845651156992000000 : ℤ) := by
  decide +kernel
end Laughlin.Certificate
end OAI
