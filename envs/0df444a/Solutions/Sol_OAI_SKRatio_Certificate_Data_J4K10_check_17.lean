-- Prove2me | solution 1 for OAI.SKRatio.Certificate.Data.J4K10.check_17
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:49:13.530992+00:00
-- url     : https://prove2.me/submissions/8f770f9e-e3b7-4c42-a9b7-e05c834d13d8

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

lemma check_17_oai : expression.check (-10+(17:ℚ)*(10*(1/20))) (1/20) 10 (blocks 17) = true := by decide +kernel

end SKRatio.Certificate.Data.J4K10

end

end OAI
end

theorem solution : type_of% @OAI.SKRatio.Certificate.Data.J4K10.check_17_oai := @OAI.SKRatio.Certificate.Data.J4K10.check_17_oai
