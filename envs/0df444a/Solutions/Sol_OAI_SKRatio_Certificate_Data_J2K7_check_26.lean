-- Prove2me | solution 1 for OAI.SKRatio.Certificate.Data.J2K7.check_26
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:20:18.461482+00:00
-- url     : https://prove2.me/submissions/26763bbd-c3f8-4cf8-adb3-50c325fca05d

import Mathlib
import Definitions.Def_OAIQ024S016

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ2K7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J2K7

lemma check_26_oai : expression.check (-10+(26:ℚ)*(5*(1/10))) (1/10) 5 (blocks 26) = true := by decide +kernel

end SKRatio.Certificate.Data.J2K7

end

end OAI
end

theorem solution : type_of% @OAI.SKRatio.Certificate.Data.J2K7.check_26_oai := @OAI.SKRatio.Certificate.Data.J2K7.check_26_oai
