-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_12_1_11_5
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T19:03:20.479599+00:00
-- url     : https://prove2.me/submissions/26104620-2904-47d4-a785-18a7b55ec1ce

import Mathlib
import Definitions.Def_OAIQ047L000

namespace OAI
namespace Laughlin.Certificate


theorem _root_.solution : RowCompute.yRowIntegralFast 12 1 11 (RowCompute.rows[5]!) =
    (60248580552944360997620075155722467975869337213928996864000000 : ℤ) := by
  decide +kernel
end Laughlin.Certificate
end OAI
