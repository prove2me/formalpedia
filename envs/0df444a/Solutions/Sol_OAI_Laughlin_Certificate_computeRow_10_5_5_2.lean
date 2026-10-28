-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_10_5_5_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:10:53.766736+00:00
-- url     : https://prove2.me/submissions/6300cc59-7a21-4230-bda6-8c10bc0ad4d3

import Mathlib
import Definitions.Def_OAIQ047L000

namespace OAI
namespace Laughlin.Certificate


theorem _root_.solution : RowCompute.yRowIntegralFast 10 5 5 (RowCompute.rows[2]!) =
    (-603365481481730605385340510478384100563901051899478016000000 : ℤ) := by
  decide +kernel
end Laughlin.Certificate
end OAI
