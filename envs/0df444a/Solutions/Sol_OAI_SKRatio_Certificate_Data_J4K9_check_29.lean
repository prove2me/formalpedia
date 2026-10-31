-- Prove2me | solution 1 for OAI.SKRatio.Certificate.Data.J4K9.check_29
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T01:05:45.264693+00:00
-- url     : https://prove2.me/submissions/9ba18f53-b599-4b16-a3f1-d5a6610bd75f

import Mathlib
import Definitions.Def_OAIQ024S011
import Definitions.Def_OAIQ024S015
import Definitions.Def_OAIQ024S016

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ4K9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J4K9

lemma check_29_oai : expression.check (-10+(29:ℚ)*(10*(1/20))) (1/20) 10 (blocks 29) = true := by decide +kernel

end SKRatio.Certificate.Data.J4K9

end

end OAI
end

theorem solution : type_of% @OAI.SKRatio.Certificate.Data.J4K9.check_29_oai := @OAI.SKRatio.Certificate.Data.J4K9.check_29_oai
