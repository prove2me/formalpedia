-- Prove2me | solution 1 for OAI.SKRatio.Certificate.Data.J2K7.check_37
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:27:04.990414+00:00
-- url     : https://prove2.me/submissions/3ae6ecb7-22ba-4e2a-9dc9-3349fb66d276

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

lemma check_37_oai : expression.check (-10+(37:ℚ)*(5*(1/10))) (1/10) 5 (blocks 37) = true := by decide +kernel

end SKRatio.Certificate.Data.J2K7

end

end OAI
end

theorem solution : type_of% @OAI.SKRatio.Certificate.Data.J2K7.check_37_oai := @OAI.SKRatio.Certificate.Data.J2K7.check_37_oai
