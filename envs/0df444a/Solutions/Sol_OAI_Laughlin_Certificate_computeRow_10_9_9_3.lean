-- Prove2me | solution 1 for OAI.Laughlin.Certificate.computeRow_10_9_9_3
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T19:49:35.240774+00:00
-- url     : https://prove2.me/submissions/4beaae3a-8af5-401f-a667-03b6a29d5a3f

import Mathlib
import Definitions.Def_OAIQ047L000

namespace OAI
namespace Laughlin.Certificate


theorem _root_.solution : RowCompute.yRowIntegralFast 10 9 9 (RowCompute.rows[3]!) =
    (33634614906074185049656350516108467795336424024693748531200000 : ℤ) := by
  decide +kernel
end Laughlin.Certificate
end OAI
