-- Prove2me | solution 1 for OAI.SKRatio.Certificate.Data.J4K8.check_24
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T00:49:11.951865+00:00
-- url     : https://prove2.me/submissions/fc37027f-443d-4c0e-a5a7-dc6dccbb5523

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

lemma check_24_oai : expression.check (-10+(24:ℚ)*(10*(1/20))) (1/20) 10 (blocks 24) = true := by decide +kernel

end SKRatio.Certificate.Data.J4K8

end

end OAI
end

theorem solution : type_of% @OAI.SKRatio.Certificate.Data.J4K8.check_24_oai := @OAI.SKRatio.Certificate.Data.J4K8.check_24_oai
