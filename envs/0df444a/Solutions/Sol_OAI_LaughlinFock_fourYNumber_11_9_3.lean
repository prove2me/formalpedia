-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_11_9_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:42:37.251945+00:00
-- url     : https://prove2.me/submissions/2984873f-6cf0-47a1-aed2-f82fb21129d0

import Mathlib
import Definitions.Def_OAIQ084L022

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate11Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate11 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem fourYNumber_11_9_3_oai :
    (collectedFourPartsTrace 11 9 3 collectedFourData_11 : ℚ) / fourCommonDenominator = (-24550910356013172596362249197/268435456000000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_11_9_3_oai := @OAI.LaughlinFock.fourYNumber_11_9_3_oai
