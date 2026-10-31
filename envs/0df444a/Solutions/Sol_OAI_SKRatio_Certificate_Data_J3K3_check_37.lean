-- Prove2me | solution 1 for OAI.SKRatio.Certificate.Data.J3K3.check_37
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:34:12.589773+00:00
-- url     : https://prove2.me/submissions/9bb8819c-c2fe-4e50-b8da-ceb7914aa954

import Mathlib
import Definitions.Def_OAIQ024S016

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ3K3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J3K3

lemma check_37_oai : expression.check (-10+(37:ℚ)*(5*(1/10))) (1/10) 5 (blocks 37) = true := by decide +kernel

end SKRatio.Certificate.Data.J3K3

end

end OAI
end

theorem solution : type_of% @OAI.SKRatio.Certificate.Data.J3K3.check_37_oai := @OAI.SKRatio.Certificate.Data.J3K3.check_37_oai
