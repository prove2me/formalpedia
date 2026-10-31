-- Prove2me | solution 1 for OAI.SKRatio.Certificate.Data.J0K3.check_37
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:37:44.10643+00:00
-- url     : https://prove2.me/submissions/b2759f1f-0ddf-4f1e-b65c-ee8598316e2c

import Mathlib
import Definitions.Def_OAIQ024S016

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ0K3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J0K3

lemma check_37_oai : expression.check (-10+(37:ℚ)*(5*(1/10))) (1/10) 5 (blocks 37) = true := by decide +kernel

end SKRatio.Certificate.Data.J0K3

end

end OAI
end

theorem solution : type_of% @OAI.SKRatio.Certificate.Data.J0K3.check_37_oai := @OAI.SKRatio.Certificate.Data.J0K3.check_37_oai
