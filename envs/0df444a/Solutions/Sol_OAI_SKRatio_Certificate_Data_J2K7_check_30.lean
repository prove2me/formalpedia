-- Prove2me | solution 1 for OAI.SKRatio.Certificate.Data.J2K7.check_30
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:23:39.988179+00:00
-- url     : https://prove2.me/submissions/bf174469-8a2c-472c-bc7c-905cda5d686f

import Mathlib
import Definitions.Def_OAIQ024S016

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ2K7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J2K7

lemma check_30_oai : expression.check (-10+(30:ℚ)*(5*(1/10))) (1/10) 5 (blocks 30) = true := by decide +kernel

end SKRatio.Certificate.Data.J2K7

end

end OAI
end

theorem solution : type_of% @OAI.SKRatio.Certificate.Data.J2K7.check_30_oai := @OAI.SKRatio.Certificate.Data.J2K7.check_30_oai
