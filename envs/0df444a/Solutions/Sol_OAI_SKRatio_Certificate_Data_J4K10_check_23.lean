-- Prove2me | solution 1 for OAI.SKRatio.Certificate.Data.J4K10.check_23
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:54:04.009832+00:00
-- url     : https://prove2.me/submissions/e12b32b3-7df9-4df0-87e3-5d80984a423c

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

lemma check_23_oai : expression.check (-10+(23:ℚ)*(10*(1/20))) (1/20) 10 (blocks 23) = true := by decide +kernel

end SKRatio.Certificate.Data.J4K10

end

end OAI
end

theorem solution : type_of% @OAI.SKRatio.Certificate.Data.J4K10.check_23_oai := @OAI.SKRatio.Certificate.Data.J4K10.check_23_oai
