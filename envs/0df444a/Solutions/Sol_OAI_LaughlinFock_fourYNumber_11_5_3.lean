-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_11_5_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:38:13.097903+00:00
-- url     : https://prove2.me/submissions/419cfa3d-0161-4605-b8a3-4a7d762ac004

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



theorem fourYNumber_11_5_3_oai :
    (collectedFourPartsTrace 11 5 3 collectedFourData_11 : ℚ) / fourCommonDenominator = (-32142369690011994391738675341/53687091200000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_11_5_3_oai := @OAI.LaughlinFock.fourYNumber_11_5_3_oai
