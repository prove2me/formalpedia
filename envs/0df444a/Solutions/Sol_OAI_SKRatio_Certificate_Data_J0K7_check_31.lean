-- Prove2me | solution 1 for OAI.SKRatio.Certificate.Data.J0K7.check_31
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:46:21.966861+00:00
-- url     : https://prove2.me/submissions/dc614837-777c-4898-bd2b-87c79c0ee88e

import Mathlib
import Definitions.Def_OAIQ024S016

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ0K7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J0K7

lemma check_31_oai : expression.check (-10+(31:ℚ)*(5*(1/10))) (1/10) 5 (blocks 31) = true := by decide +kernel

end SKRatio.Certificate.Data.J0K7

end

end OAI
end

theorem solution : type_of% @OAI.SKRatio.Certificate.Data.J0K7.check_31_oai := @OAI.SKRatio.Certificate.Data.J0K7.check_31_oai
