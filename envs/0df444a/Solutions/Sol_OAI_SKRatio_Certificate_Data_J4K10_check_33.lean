-- Prove2me | solution 1 for OAI.SKRatio.Certificate.Data.J4K10.check_33
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:58:13.573385+00:00
-- url     : https://prove2.me/submissions/4fb30a66-fc0a-4afd-a916-7d8291416c42

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

lemma check_33_oai : expression.check (-10+(33:ℚ)*(10*(1/20))) (1/20) 10 (blocks 33) = true := by decide +kernel

end SKRatio.Certificate.Data.J4K10

end

end OAI
end

theorem solution : type_of% @OAI.SKRatio.Certificate.Data.J4K10.check_33_oai := @OAI.SKRatio.Certificate.Data.J4K10.check_33_oai
