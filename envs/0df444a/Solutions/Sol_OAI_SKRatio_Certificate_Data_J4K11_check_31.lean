-- Prove2me | solution 1 for OAI.SKRatio.Certificate.Data.J4K11.check_31
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T00:11:48.030054+00:00
-- url     : https://prove2.me/submissions/a98aeb05-6f8c-4970-8e8f-5a451b0b9c73

import Mathlib
import Definitions.Def_OAIQ024S011
import Definitions.Def_OAIQ024S016

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ4K11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J4K11

lemma check_31_oai : expression.check (-10+(31:ℚ)*(10*(1/20))) (1/20) 10 (blocks 31) = true := by decide +kernel

end SKRatio.Certificate.Data.J4K11

end

end OAI
end

theorem solution : type_of% @OAI.SKRatio.Certificate.Data.J4K11.check_31_oai := @OAI.SKRatio.Certificate.Data.J4K11.check_31_oai
