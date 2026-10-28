-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_10_3_7_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:11:13.26754+00:00
-- url     : https://prove2.me/submissions/dd0d21ee-de12-497c-90a2-5661ec5eefc4

import Mathlib
import Definitions.Def_OAIQ047L000

namespace OAI
namespace Laughlin.Certificate


theorem _root_.solution : RowCompute.yRowIntegralFast 10 3 7 (RowCompute.rows[1]!) =
    (-682910588311277775361033593651028530229655891450265600000 : ℤ) := by
  decide +kernel
end Laughlin.Certificate
end OAI
