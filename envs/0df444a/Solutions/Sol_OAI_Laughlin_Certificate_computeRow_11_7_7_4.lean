-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_11_7_7_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T19:04:53.191574+00:00
-- url     : https://prove2.me/submissions/8a199305-3f2b-49ee-b7e0-5307d5f553aa

import Mathlib
import Definitions.Def_OAIQ047L000

namespace OAI
namespace Laughlin.Certificate


theorem _root_.solution : RowCompute.yRowIntegralFast 11 7 7 (RowCompute.rows[4]!) =
    (143699654238536405363840915962921238865512385576802713600000 : ℤ) := by
  decide +kernel
end Laughlin.Certificate
end OAI
