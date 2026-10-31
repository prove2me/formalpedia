-- Prove2me | solution 1 for OAI.SKRatio.Certificate.Data.J4K12.check_24
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T00:17:10.605822+00:00
-- url     : https://prove2.me/submissions/93df42a0-f5b9-44c9-8559-c48ed7bab4a4

import Mathlib
import Definitions.Def_OAIQ024S012
import Definitions.Def_OAIQ024S016

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ4K12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J4K12

lemma check_24_oai : expression.check (-10+(24:ℚ)*(10*(1/20))) (1/20) 10 (blocks 24) = true := by decide +kernel

end SKRatio.Certificate.Data.J4K12

end

end OAI
end

theorem solution : type_of% @OAI.SKRatio.Certificate.Data.J4K12.check_24_oai := @OAI.SKRatio.Certificate.Data.J4K12.check_24_oai
