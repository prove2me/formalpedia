-- Prove2me | solution 1 for OAI.SKRatio.Certificate.Data.J0K3.check_36
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:37:21.197279+00:00
-- url     : https://prove2.me/submissions/bc1b47af-0e12-42e4-a0ad-8319e2d1630b

import Mathlib
import Definitions.Def_OAIQ024S016

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ0K3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J0K3

lemma check_36_oai : expression.check (-10+(36:ℚ)*(5*(1/10))) (1/10) 5 (blocks 36) = true := by decide +kernel

end SKRatio.Certificate.Data.J0K3

end

end OAI
end

theorem solution : type_of% @OAI.SKRatio.Certificate.Data.J0K3.check_36_oai := @OAI.SKRatio.Certificate.Data.J0K3.check_36_oai
