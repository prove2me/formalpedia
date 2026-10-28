-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_10_5_9_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T19:49:59.581165+00:00
-- url     : https://prove2.me/submissions/7a579d96-e5a8-4106-805d-623df3ec3237

import Mathlib
import Definitions.Def_OAIQ047L000

namespace OAI
namespace Laughlin.Certificate


theorem _root_.solution : RowCompute.yRowIntegralFast 10 5 9 (RowCompute.rows[1]!) =
    (2371656610966962636101923122578277087114996844855296000000 : ℤ) := by
  decide +kernel
end Laughlin.Certificate
end OAI
