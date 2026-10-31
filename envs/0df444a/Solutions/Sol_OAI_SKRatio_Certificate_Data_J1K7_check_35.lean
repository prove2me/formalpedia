-- Prove2me | solution 1 for OAI.SKRatio.Certificate.Data.J1K7.check_35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:06:20.555878+00:00
-- url     : https://prove2.me/submissions/76e5d4cd-69a8-4c43-b36c-0185e143aa64

import Mathlib
import Definitions.Def_OAIQ024S016

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ1K7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J1K7

lemma check_35_oai : expression.check (-10+(35:ℚ)*(5*(1/10))) (1/10) 5 (blocks 35) = true := by decide +kernel

end SKRatio.Certificate.Data.J1K7

end

end OAI
end

theorem solution : type_of% @OAI.SKRatio.Certificate.Data.J1K7.check_35_oai := @OAI.SKRatio.Certificate.Data.J1K7.check_35_oai
