-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_11_3_7_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T19:15:22.627982+00:00
-- url     : https://prove2.me/submissions/12641860-73fc-4b3c-b94e-8d93fa77b736

import Mathlib
import Definitions.Def_OAIQ047L000

namespace OAI
namespace Laughlin.Certificate


theorem _root_.solution : RowCompute.yRowIntegralFast 11 3 7 (RowCompute.rows[3]!) =
    (-227254234050595480010707800531343133180415234842768179200000 : ℤ) := by
  decide +kernel
end Laughlin.Certificate
end OAI
