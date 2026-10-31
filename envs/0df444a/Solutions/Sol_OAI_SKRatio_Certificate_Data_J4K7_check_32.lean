-- Prove2me | solution 1 for OAI.SKRatio.Certificate.Data.J4K7.check_32
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T00:38:34.01799+00:00
-- url     : https://prove2.me/submissions/00992180-7efa-4277-af66-d924895aafb0

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

lemma check_32_oai : expression.check (-10+(32:ℚ)*(5*(1/10))) (1/10) 5 (blocks 32) = true := by decide +kernel

end SKRatio.Certificate.Data.J4K7

end

end OAI
end

theorem solution : type_of% @OAI.SKRatio.Certificate.Data.J4K7.check_32_oai := @OAI.SKRatio.Certificate.Data.J4K7.check_32_oai
