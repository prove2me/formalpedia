-- Prove2me | solution 1 for OAI.SKRatio.Certificate.Data.J4K10.check_34
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:58:14.637036+00:00
-- url     : https://prove2.me/submissions/d1234dc2-1c9a-4599-a972-4f27497e9c37

import Mathlib
import Definitions.Def_OAIQ024S016

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ4K10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J4K10

lemma check_34_oai : expression.check (-10+(34:ℚ)*(10*(1/20))) (1/20) 10 (blocks 34) = true := by decide +kernel

end SKRatio.Certificate.Data.J4K10

end

end OAI
end

theorem solution : type_of% @OAI.SKRatio.Certificate.Data.J4K10.check_34_oai := @OAI.SKRatio.Certificate.Data.J4K10.check_34_oai
