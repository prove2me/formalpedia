-- Prove2me | solution 1 for OAI.SKRatio.Certificate.Data.J4K7.check_35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T00:39:20.61601+00:00
-- url     : https://prove2.me/submissions/feb96c0e-b730-4d10-89d4-789869ba2b1b

import Mathlib
import Definitions.Def_OAIQ024S013
import Definitions.Def_OAIQ024S016

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ4K7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J4K7

lemma check_35_oai : expression.check (-10+(35:ℚ)*(5*(1/10))) (1/10) 5 (blocks 35) = true := by decide +kernel

end SKRatio.Certificate.Data.J4K7

end

end OAI
end

theorem solution : type_of% @OAI.SKRatio.Certificate.Data.J4K7.check_35_oai := @OAI.SKRatio.Certificate.Data.J4K7.check_35_oai
