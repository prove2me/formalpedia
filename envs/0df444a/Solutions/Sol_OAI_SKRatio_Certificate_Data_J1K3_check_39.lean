-- Prove2me | solution 1 for OAI.SKRatio.Certificate.Data.J1K3.check_39
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:57:39.231272+00:00
-- url     : https://prove2.me/submissions/c4e0b2c2-db7d-450d-9050-90a74e774f9d

import Mathlib
import Definitions.Def_OAIQ024S016

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ1K3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J1K3

lemma check_39_oai : expression.check (-10+(39:ℚ)*(5*(1/10))) (1/10) 5 (blocks 39) = true := by decide +kernel

end SKRatio.Certificate.Data.J1K3

end

end OAI
end

theorem solution : type_of% @OAI.SKRatio.Certificate.Data.J1K3.check_39_oai := @OAI.SKRatio.Certificate.Data.J1K3.check_39_oai
