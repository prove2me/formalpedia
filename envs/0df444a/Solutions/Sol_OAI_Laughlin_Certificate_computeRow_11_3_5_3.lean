-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_11_3_5_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T19:15:36.651555+00:00
-- url     : https://prove2.me/submissions/9753e7ab-2a22-446d-af2c-b3c19e92eecf

import Mathlib
import Definitions.Def_OAIQ047L000

namespace OAI
namespace Laughlin.Certificate


theorem _root_.solution : RowCompute.yRowIntegralFast 11 3 5 (RowCompute.rows[3]!) =
    (2725308543630810518843960007128921290037690595482271744000000 : ℤ) := by
  decide +kernel
end Laughlin.Certificate
end OAI
