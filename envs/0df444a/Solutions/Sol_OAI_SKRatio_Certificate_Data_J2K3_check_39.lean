-- Prove2me | solution 1 for OAI.SKRatio.Certificate.Data.J2K3.check_39
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:14:43.545731+00:00
-- url     : https://prove2.me/submissions/e0cf897c-aead-4877-9fe2-2db38b1bb0f6

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

lemma check_39_oai : expression.check (-10+(39:ℚ)*(5*(1/10))) (1/10) 5 (blocks 39) = true := by decide +kernel

end SKRatio.Certificate.Data.J2K3

end

end OAI
end

theorem solution : type_of% @OAI.SKRatio.Certificate.Data.J2K3.check_39_oai := @OAI.SKRatio.Certificate.Data.J2K3.check_39_oai
