-- Prove2me | solution 1 for OAI.SKRatio.Certificate.Data.J4K8.check_33
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T00:53:42.667776+00:00
-- url     : https://prove2.me/submissions/5715c9c1-ea50-44a7-9a18-f747a363ff0e

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

lemma check_33_oai : expression.check (-10+(33:ℚ)*(10*(1/20))) (1/20) 10 (blocks 33) = true := by decide +kernel

end SKRatio.Certificate.Data.J4K8

end

end OAI
end

theorem solution : type_of% @OAI.SKRatio.Certificate.Data.J4K8.check_33_oai := @OAI.SKRatio.Certificate.Data.J4K8.check_33_oai
