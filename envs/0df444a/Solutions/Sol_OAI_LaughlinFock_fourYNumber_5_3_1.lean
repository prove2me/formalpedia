-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_5_3_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T18:43:37.665991+00:00
-- url     : https://prove2.me/submissions/d3c02513-82ab-4aa7-84ac-88059c6ec124

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



theorem fourYNumber_5_3_1_oai :
    (shortNumericRowsFourTrace 5 3 1 : ℚ) / fourCommonDenominator = (61749543313564923991586775801/601295421440000000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_5_3_1_oai := @OAI.LaughlinFock.fourYNumber_5_3_1_oai
