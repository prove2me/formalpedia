-- Prove2me | solution 1 for OAI.SKRatio.Certificate.Data.J2K7.check_33
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:24:48.786741+00:00
-- url     : https://prove2.me/submissions/24c23b45-f0bc-468c-99e7-988ca31700f8

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

lemma check_33_oai : expression.check (-10+(33:ℚ)*(5*(1/10))) (1/10) 5 (blocks 33) = true := by decide +kernel

end SKRatio.Certificate.Data.J2K7

end

end OAI
end

theorem solution : type_of% @OAI.SKRatio.Certificate.Data.J2K7.check_33_oai := @OAI.SKRatio.Certificate.Data.J2K7.check_33_oai
