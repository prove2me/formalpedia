-- Prove2me | solution 1 for OAI.SKRatio.Certificate.Data.J4K9.check_12
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T00:57:28.700988+00:00
-- url     : https://prove2.me/submissions/d5728940-ebba-43a9-a53d-a19862e7baeb

import Mathlib
import Definitions.Def_OAIQ024S011
import Definitions.Def_OAIQ024S015
import Definitions.Def_OAIQ024S016

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ4K9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J4K9

lemma check_12_oai : expression.check (-10+(12:ℚ)*(10*(1/20))) (1/20) 10 (blocks 12) = true := by decide +kernel

end SKRatio.Certificate.Data.J4K9

end

end OAI
end

theorem solution : type_of% @OAI.SKRatio.Certificate.Data.J4K9.check_12_oai := @OAI.SKRatio.Certificate.Data.J4K9.check_12_oai
