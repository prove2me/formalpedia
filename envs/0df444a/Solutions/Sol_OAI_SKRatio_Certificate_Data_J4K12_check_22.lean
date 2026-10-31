-- Prove2me | solution 1 for OAI.SKRatio.Certificate.Data.J4K12.check_22
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T00:15:38.157904+00:00
-- url     : https://prove2.me/submissions/c4d227cb-606b-4e97-b877-836bf7f4ae8d

import Mathlib
import Definitions.Def_OAIQ024S012
import Definitions.Def_OAIQ024S016

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ4K12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J4K12

lemma check_22_oai : expression.check (-10+(22:ℚ)*(10*(1/20))) (1/20) 10 (blocks 22) = true := by decide +kernel

end SKRatio.Certificate.Data.J4K12

end

end OAI
end

theorem solution : type_of% @OAI.SKRatio.Certificate.Data.J4K12.check_22_oai := @OAI.SKRatio.Certificate.Data.J4K12.check_22_oai
