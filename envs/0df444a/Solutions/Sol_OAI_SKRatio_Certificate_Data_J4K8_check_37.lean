-- Prove2me | solution 1 for OAI.SKRatio.Certificate.Data.J4K8.check_37
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T00:55:35.589508+00:00
-- url     : https://prove2.me/submissions/72e56664-33a1-4cd0-8981-5f7cd2567721

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

lemma check_37_oai : expression.check (-10+(37:ℚ)*(10*(1/20))) (1/20) 10 (blocks 37) = true := by decide +kernel

end SKRatio.Certificate.Data.J4K8

end

end OAI
end

theorem solution : type_of% @OAI.SKRatio.Certificate.Data.J4K8.check_37_oai := @OAI.SKRatio.Certificate.Data.J4K8.check_37_oai
