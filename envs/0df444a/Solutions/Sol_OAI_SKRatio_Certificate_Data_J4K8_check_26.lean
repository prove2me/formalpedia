-- Prove2me | solution 1 for OAI.SKRatio.Certificate.Data.J4K8.check_26
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T00:50:19.219216+00:00
-- url     : https://prove2.me/submissions/5604a73e-8e1b-4ebd-b586-315277ae31f6

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

lemma check_26_oai : expression.check (-10+(26:ℚ)*(10*(1/20))) (1/20) 10 (blocks 26) = true := by decide +kernel

end SKRatio.Certificate.Data.J4K8

end

end OAI
end

theorem solution : type_of% @OAI.SKRatio.Certificate.Data.J4K8.check_26_oai := @OAI.SKRatio.Certificate.Data.J4K8.check_26_oai
