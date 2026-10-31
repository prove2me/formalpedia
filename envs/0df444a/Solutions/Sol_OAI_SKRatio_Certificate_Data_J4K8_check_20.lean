-- Prove2me | solution 1 for OAI.SKRatio.Certificate.Data.J4K8.check_20
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T00:47:40.378215+00:00
-- url     : https://prove2.me/submissions/d1ab684a-c443-41ba-b2db-455f214fe6f3

import Mathlib
import Definitions.Def_OAIQ024S013
import Definitions.Def_OAIQ024S014
import Definitions.Def_OAIQ024S016

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ4K8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J4K8

lemma check_20_oai : expression.check (-10+(20:ℚ)*(10*(1/20))) (1/20) 10 (blocks 20) = true := by decide +kernel

end SKRatio.Certificate.Data.J4K8

end

end OAI
end

theorem solution : type_of% @OAI.SKRatio.Certificate.Data.J4K8.check_20_oai := @OAI.SKRatio.Certificate.Data.J4K8.check_20_oai
