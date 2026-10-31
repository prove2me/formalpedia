-- Prove2me | solution 1 for OAI.SKRatio.Certificate.Data.J4K10.check_19
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:51:04.975599+00:00
-- url     : https://prove2.me/submissions/a987bc92-9740-4c45-9a09-3073738c9913

import Mathlib
import Definitions.Def_OAIQ024S016

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ4K10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J4K10

lemma check_19_oai : expression.check (-10+(19:ℚ)*(10*(1/20))) (1/20) 10 (blocks 19) = true := by decide +kernel

end SKRatio.Certificate.Data.J4K10

end

end OAI
end

theorem solution : type_of% @OAI.SKRatio.Certificate.Data.J4K10.check_19_oai := @OAI.SKRatio.Certificate.Data.J4K10.check_19_oai
