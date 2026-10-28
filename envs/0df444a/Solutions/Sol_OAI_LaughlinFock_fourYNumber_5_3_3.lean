-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_5_3_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T18:43:38.799732+00:00
-- url     : https://prove2.me/submissions/bee3ae57-04ce-42be-a5ce-beafeedce9d1

import Mathlib
import Definitions.Def_OAIQ084L015

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate05Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate05 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem fourYNumber_5_3_3_oai :
    (shortNumericRowsFourTrace 5 3 3 : ℚ) / fourCommonDenominator = (-81625478502088057676049676411/1202590842880000000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_5_3_3_oai := @OAI.LaughlinFock.fourYNumber_5_3_3_oai
