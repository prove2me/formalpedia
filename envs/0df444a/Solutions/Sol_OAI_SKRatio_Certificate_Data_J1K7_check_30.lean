-- Prove2me | solution 1 for OAI.SKRatio.Certificate.Data.J1K7.check_30
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:03:41.106097+00:00
-- url     : https://prove2.me/submissions/c1360993-c765-4fd5-a48c-0957be0abccc

import Mathlib
import Definitions.Def_OAIQ024S016

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ1K7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J1K7

lemma check_30_oai : expression.check (-10+(30:ℚ)*(5*(1/10))) (1/10) 5 (blocks 30) = true := by decide +kernel

end SKRatio.Certificate.Data.J1K7

end

end OAI
end

theorem solution : type_of% @OAI.SKRatio.Certificate.Data.J1K7.check_30_oai := @OAI.SKRatio.Certificate.Data.J1K7.check_30_oai
