-- Prove2me | solution 1 for OAI.SKRatio.Certificate.Data.J4K3.check_33
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T00:25:30.441848+00:00
-- url     : https://prove2.me/submissions/aa98ddb9-d38e-490e-8d7c-838be8ab2c7b

import Mathlib
import Definitions.Def_OAIQ024S012
import Definitions.Def_OAIQ024S016

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ4K3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J4K3

lemma check_33_oai : expression.check (-10+(33:ℚ)*(5*(1/10))) (1/10) 5 (blocks 33) = true := by decide +kernel

end SKRatio.Certificate.Data.J4K3

end

end OAI
end

theorem solution : type_of% @OAI.SKRatio.Certificate.Data.J4K3.check_33_oai := @OAI.SKRatio.Certificate.Data.J4K3.check_33_oai
