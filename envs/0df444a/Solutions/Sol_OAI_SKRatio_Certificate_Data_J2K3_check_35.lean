-- Prove2me | solution 1 for OAI.SKRatio.Certificate.Data.J2K3.check_35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:10:59.636428+00:00
-- url     : https://prove2.me/submissions/8375e845-0dc8-435d-bf52-2628628bd661

import Mathlib
import Definitions.Def_OAIQ024S016

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ2K3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J2K3

lemma check_35_oai : expression.check (-10+(35:ℚ)*(5*(1/10))) (1/10) 5 (blocks 35) = true := by decide +kernel

end SKRatio.Certificate.Data.J2K3

end

end OAI
end

theorem solution : type_of% @OAI.SKRatio.Certificate.Data.J2K3.check_35_oai := @OAI.SKRatio.Certificate.Data.J2K3.check_35_oai
