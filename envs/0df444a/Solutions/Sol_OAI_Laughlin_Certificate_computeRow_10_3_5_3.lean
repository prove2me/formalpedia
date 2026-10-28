-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_10_3_5_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T20:11:16.573411+00:00
-- url     : https://prove2.me/submissions/2e436465-d86c-42a8-a453-c281b1bbb88c

import Mathlib
import Definitions.Def_OAIQ047L000

namespace OAI
namespace Laughlin.Certificate


theorem _root_.solution : RowCompute.yRowIntegralFast 10 3 5 (RowCompute.rows[3]!) =
    (350692429224228994729601048816271473106160261917573120000000 : ℤ) := by
  decide +kernel
end Laughlin.Certificate
end OAI
