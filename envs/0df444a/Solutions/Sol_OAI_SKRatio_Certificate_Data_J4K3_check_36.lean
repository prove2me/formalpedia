-- Prove2me | solution 1 for OAI.SKRatio.Certificate.Data.J4K3.check_36
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T00:27:22.477272+00:00
-- url     : https://prove2.me/submissions/8b88f87e-dcd5-4ab6-b59b-1ecbf98f9aea

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

lemma check_36_oai : expression.check (-10+(36:ℚ)*(5*(1/10))) (1/10) 5 (blocks 36) = true := by decide +kernel

end SKRatio.Certificate.Data.J4K3

end

end OAI
end

theorem solution : type_of% @OAI.SKRatio.Certificate.Data.J4K3.check_36_oai := @OAI.SKRatio.Certificate.Data.J4K3.check_36_oai
