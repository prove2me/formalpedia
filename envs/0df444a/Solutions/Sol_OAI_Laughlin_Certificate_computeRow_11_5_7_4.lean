-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_11_5_7_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T19:11:11.508459+00:00
-- url     : https://prove2.me/submissions/7b3a3e59-ef1e-4ce4-a81d-5b018529b9c0

import Mathlib
import Definitions.Def_OAIQ047L000

namespace OAI
namespace Laughlin.Certificate


theorem _root_.solution : RowCompute.yRowIntegralFast 11 5 7 (RowCompute.rows[4]!) =
    (-162393274643170663398083245488426435807277115536048128000000 : ℤ) := by
  decide +kernel
end Laughlin.Certificate
end OAI
