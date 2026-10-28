-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_14_5_5
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:57:30.286708+00:00
-- url     : https://prove2.me/submissions/15d296ff-5f5a-4684-b2eb-e8dd59d43714

import Mathlib
import Definitions.Def_OAIQ084L022

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate14Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate14 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem fourYNumber_14_5_5_oai :
    (collectedFourPartsTrace 14 5 5 collectedFourData_14 : ℚ) / fourCommonDenominator = (-118599109885276691436463501647/6710886400000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_14_5_5_oai := @OAI.LaughlinFock.fourYNumber_14_5_5_oai
