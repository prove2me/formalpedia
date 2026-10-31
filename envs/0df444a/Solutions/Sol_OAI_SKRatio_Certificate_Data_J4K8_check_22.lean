-- Prove2me | solution 1 for OAI.SKRatio.Certificate.Data.J4K8.check_22
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T00:48:26.030949+00:00
-- url     : https://prove2.me/submissions/0d9e6eee-df95-48b9-bcdc-ed84015d77aa

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

lemma check_22_oai : expression.check (-10+(22:ℚ)*(10*(1/20))) (1/20) 10 (blocks 22) = true := by decide +kernel

end SKRatio.Certificate.Data.J4K8

end

end OAI
end

theorem solution : type_of% @OAI.SKRatio.Certificate.Data.J4K8.check_22_oai := @OAI.SKRatio.Certificate.Data.J4K8.check_22_oai
