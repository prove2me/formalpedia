-- Prove2me | solution 1 for OAI.SKRatio.Certificate.Data.J3K7.check_29
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:41:18.115788+00:00
-- url     : https://prove2.me/submissions/b3e30248-fa4c-43fe-896b-3523ac8a0116

import Mathlib
import Definitions.Def_OAIQ024S016

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ3K7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J3K7

lemma check_29_oai : expression.check (-10+(29:ℚ)*(5*(1/10))) (1/10) 5 (blocks 29) = true := by decide +kernel

end SKRatio.Certificate.Data.J3K7

end

end OAI
end

theorem solution : type_of% @OAI.SKRatio.Certificate.Data.J3K7.check_29_oai := @OAI.SKRatio.Certificate.Data.J3K7.check_29_oai
