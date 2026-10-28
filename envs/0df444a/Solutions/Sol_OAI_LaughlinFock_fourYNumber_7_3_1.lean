-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_7_3_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T18:46:36.154399+00:00
-- url     : https://prove2.me/submissions/4149b28b-e084-4a4d-8679-a74bfc0bf312

import Mathlib
import Definitions.Def_OAIQ084L015

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate07Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate07 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem fourYNumber_7_3_1_oai :
    (shortNumericRowsFourTrace 7 3 1 : ℚ) / fourCommonDenominator = (45995705370248318526416296167/7516192768000000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_7_3_1_oai := @OAI.LaughlinFock.fourYNumber_7_3_1_oai
