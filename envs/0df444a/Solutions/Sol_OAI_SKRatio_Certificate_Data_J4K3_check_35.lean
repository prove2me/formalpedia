-- Prove2me | solution 1 for OAI.SKRatio.Certificate.Data.J4K3.check_35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T00:26:59.661066+00:00
-- url     : https://prove2.me/submissions/a2b4bafc-d035-42c7-97f2-fcca288f1cd8

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

lemma check_35_oai : expression.check (-10+(35:ℚ)*(5*(1/10))) (1/10) 5 (blocks 35) = true := by decide +kernel

end SKRatio.Certificate.Data.J4K3

end

end OAI
end

theorem solution : type_of% @OAI.SKRatio.Certificate.Data.J4K3.check_35_oai := @OAI.SKRatio.Certificate.Data.J4K3.check_35_oai
