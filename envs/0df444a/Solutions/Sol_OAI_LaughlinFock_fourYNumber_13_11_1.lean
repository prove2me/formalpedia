-- Prove2me | solution 1 for OAI.LaughlinFock.fourYNumber_13_11_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:44:07.567199+00:00
-- url     : https://prove2.me/submissions/e626c250-5aa3-47b0-9e57-ef866dffefd0

import Mathlib
import Definitions.Def_OAIQ084L022

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate13Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate13 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem fourYNumber_13_11_1_oai :
    (collectedFourPartsTrace 13 11 1 collectedFourData_13 : ℚ) / fourCommonDenominator = (2144660569773776567544859885431/26843545600000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYNumber_13_11_1_oai := @OAI.LaughlinFock.fourYNumber_13_11_1_oai
