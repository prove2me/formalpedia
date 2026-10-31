-- Prove2me | solution 1 for OAI.SKRatio.Certificate.Data.J4K3.check_39
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T00:29:16.69042+00:00
-- url     : https://prove2.me/submissions/ca52c3ad-ec05-4d6a-8ce3-e81ccabe12ef

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

lemma check_39_oai : expression.check (-10+(39:ℚ)*(5*(1/10))) (1/10) 5 (blocks 39) = true := by decide +kernel

end SKRatio.Certificate.Data.J4K3

end

end OAI
end

theorem solution : type_of% @OAI.SKRatio.Certificate.Data.J4K3.check_39_oai := @OAI.SKRatio.Certificate.Data.J4K3.check_39_oai
