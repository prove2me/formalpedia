-- Prove2me | solution 1 for OAI.SKRatio.Certificate.Data.J4K9.check_25
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T01:03:52.587566+00:00
-- url     : https://prove2.me/submissions/88e14636-ab20-41a5-bc07-87cafd00dc3f

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

lemma check_25_oai : expression.check (-10+(25:ℚ)*(10*(1/20))) (1/20) 10 (blocks 25) = true := by decide +kernel

end SKRatio.Certificate.Data.J4K9

end

end OAI
end

theorem solution : type_of% @OAI.SKRatio.Certificate.Data.J4K9.check_25_oai := @OAI.SKRatio.Certificate.Data.J4K9.check_25_oai
