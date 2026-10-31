-- Prove2me | solution 1 for OAI.SKRatio.Certificate.Data.J4K11.check_28
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T00:09:55.715279+00:00
-- url     : https://prove2.me/submissions/2091b601-b6b6-4f8b-b20a-a16f5dfbee79

import Mathlib
import Definitions.Def_OAIQ024S011
import Definitions.Def_OAIQ024S016

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ4K11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J4K11

lemma check_28_oai : expression.check (-10+(28:ℚ)*(10*(1/20))) (1/20) 10 (blocks 28) = true := by decide +kernel

end SKRatio.Certificate.Data.J4K11

end

end OAI
end

theorem solution : type_of% @OAI.SKRatio.Certificate.Data.J4K11.check_28_oai := @OAI.SKRatio.Certificate.Data.J4K11.check_28_oai
