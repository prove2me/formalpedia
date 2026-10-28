-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_10_5_5
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T18:27:58.079385+00:00
-- url     : https://prove2.me/submissions/f6b68af5-c027-4c91-a291-976e80730734

import Mathlib
import Definitions.Def_OAIQ084L002
import Definitions.Def_OAIQ084L009

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate10Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate10 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem fourYNumber_10_5_5_oai :
    (collectedFourPartsTrace 10 5 5 collectedFourData_10 : ℚ) / fourCommonDenominator = (4916058814322941309449723117/107374182400000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_10_5_5_oai := @OAI.LaughlinFock.fourYNumber_10_5_5_oai
