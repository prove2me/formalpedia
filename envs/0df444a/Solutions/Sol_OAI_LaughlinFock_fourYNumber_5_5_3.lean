-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_5_5_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T18:43:39.679571+00:00
-- url     : https://prove2.me/submissions/0cd3c7b7-36c7-477b-bf7f-15752d8741f0

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



theorem fourYNumber_5_5_3_oai :
    (shortNumericRowsFourTrace 5 5 3 : ℚ) / fourCommonDenominator = (6370708288009007294968493697/120259084288000000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_5_5_3_oai := @OAI.LaughlinFock.fourYNumber_5_5_3_oai
