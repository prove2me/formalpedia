-- Prove2me | solution 1 for OAI.SKRatio.Certificate.Data.J4K12.check_30
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T00:20:34.46053+00:00
-- url     : https://prove2.me/submissions/d4b80e10-5827-430b-b401-49564b1ed0fc

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

lemma check_30_oai : expression.check (-10+(30:ℚ)*(10*(1/20))) (1/20) 10 (blocks 30) = true := by decide +kernel

end SKRatio.Certificate.Data.J4K12

end

end OAI
end

theorem solution : type_of% @OAI.SKRatio.Certificate.Data.J4K12.check_30_oai := @OAI.SKRatio.Certificate.Data.J4K12.check_30_oai
