-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_11_5_9_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T19:11:08.526197+00:00
-- url     : https://prove2.me/submissions/7ba85ab2-fd72-4232-be10-04c53f026fb6

import Mathlib
import Definitions.Def_OAIQ047L000

namespace OAI
namespace Laughlin.Certificate


theorem _root_.solution : RowCompute.yRowIntegralFast 11 5 9 (RowCompute.rows[1]!) =
    (6818080018770595105409500165705206309490382962950144000000 : ℤ) := by
  decide +kernel
end Laughlin.Certificate
end OAI
