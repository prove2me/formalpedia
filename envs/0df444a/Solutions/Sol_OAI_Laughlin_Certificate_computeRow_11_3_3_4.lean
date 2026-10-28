-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_11_3_3_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T19:15:39.690436+00:00
-- url     : https://prove2.me/submissions/0bec4f30-4c3b-4102-ad50-0fbebd4d7297

import Mathlib
import Definitions.Def_OAIQ047L000

namespace OAI
namespace Laughlin.Certificate


theorem _root_.solution : RowCompute.yRowIntegralFast 11 3 3 (RowCompute.rows[4]!) =
    (145587321786441247428223561316822950002156873727554355200000 : ℤ) := by
  decide +kernel
end Laughlin.Certificate
end OAI
