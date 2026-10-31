-- Prove2me | solution 1 for OAI.SKRatio.Certificate.Data.J4K11.check_27
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T00:09:54.695584+00:00
-- url     : https://prove2.me/submissions/2b8ec44b-c9de-4d32-a8d4-424431251565

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

lemma check_27_oai : expression.check (-10+(27:ℚ)*(10*(1/20))) (1/20) 10 (blocks 27) = true := by decide +kernel

end SKRatio.Certificate.Data.J4K11

end

end OAI
end

theorem solution : type_of% @OAI.SKRatio.Certificate.Data.J4K11.check_27_oai := @OAI.SKRatio.Certificate.Data.J4K11.check_27_oai
