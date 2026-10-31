-- Prove2me | solution 1 for OAI.SKRatio.Certificate.Data.J4K10.check_27
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:55:57.058629+00:00
-- url     : https://prove2.me/submissions/3f26a05e-b379-4609-8a65-82cd3b11bc69

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

lemma check_27_oai : expression.check (-10+(27:ℚ)*(10*(1/20))) (1/20) 10 (blocks 27) = true := by decide +kernel

end SKRatio.Certificate.Data.J4K10

end

end OAI
end

theorem solution : type_of% @OAI.SKRatio.Certificate.Data.J4K10.check_27_oai := @OAI.SKRatio.Certificate.Data.J4K10.check_27_oai
