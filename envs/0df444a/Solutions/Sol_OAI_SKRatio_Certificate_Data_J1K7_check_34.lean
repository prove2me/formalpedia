-- Prove2me | solution 1 for OAI.SKRatio.Certificate.Data.J1K7.check_34
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:05:13.615003+00:00
-- url     : https://prove2.me/submissions/3614e742-c86a-4413-802a-9e4fc589591e

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

lemma check_34_oai : expression.check (-10+(34:ℚ)*(5*(1/10))) (1/10) 5 (blocks 34) = true := by decide +kernel

end SKRatio.Certificate.Data.J1K7

end

end OAI
end

theorem solution : type_of% @OAI.SKRatio.Certificate.Data.J1K7.check_34_oai := @OAI.SKRatio.Certificate.Data.J1K7.check_34_oai
