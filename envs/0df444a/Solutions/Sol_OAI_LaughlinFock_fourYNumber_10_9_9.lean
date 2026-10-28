-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_10_9_9
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T18:34:02.830997+00:00
-- url     : https://prove2.me/submissions/0312c175-fda4-4601-84a7-3adf8a661c9e

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



theorem fourYNumber_10_9_9_oai :
    (collectedFourPartsTrace 10 9 9 collectedFourData_10 : ℚ) / fourCommonDenominator = (-34263985364968403855161804941/268435456000000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_10_9_9_oai := @OAI.LaughlinFock.fourYNumber_10_9_9_oai
