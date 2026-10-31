-- Prove2me | solution 1 for OAI.SKRatio.Certificate.Data.J4K12.check_27
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T00:18:41.552812+00:00
-- url     : https://prove2.me/submissions/4deafac2-5a91-4056-bd46-b341a5a0343e

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

lemma check_27_oai : expression.check (-10+(27:ℚ)*(10*(1/20))) (1/20) 10 (blocks 27) = true := by decide +kernel

end SKRatio.Certificate.Data.J4K12

end

end OAI
end

theorem solution : type_of% @OAI.SKRatio.Certificate.Data.J4K12.check_27_oai := @OAI.SKRatio.Certificate.Data.J4K12.check_27_oai
