-- Prove2me | solution 1 for OAI.SKRatio.Certificate.Data.J4K10.check_30
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:56:21.830978+00:00
-- url     : https://prove2.me/submissions/9385783b-ab98-4da2-a13e-ed04850a6ac5

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

lemma check_30_oai : expression.check (-10+(30:ℚ)*(10*(1/20))) (1/20) 10 (blocks 30) = true := by decide +kernel

end SKRatio.Certificate.Data.J4K10

end

end OAI
end

theorem solution : type_of% @OAI.SKRatio.Certificate.Data.J4K10.check_30_oai := @OAI.SKRatio.Certificate.Data.J4K10.check_30_oai
