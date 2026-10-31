-- Prove2me | solution 1 for OAI.SKRatio.Certificate.Data.J4K7.check_28
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T00:36:40.672983+00:00
-- url     : https://prove2.me/submissions/b5e3359a-f2b6-41d4-9991-bcbf32a4001f

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

lemma check_28_oai : expression.check (-10+(28:ℚ)*(5*(1/10))) (1/10) 5 (blocks 28) = true := by decide +kernel

end SKRatio.Certificate.Data.J4K7

end

end OAI
end

theorem solution : type_of% @OAI.SKRatio.Certificate.Data.J4K7.check_28_oai := @OAI.SKRatio.Certificate.Data.J4K7.check_28_oai
