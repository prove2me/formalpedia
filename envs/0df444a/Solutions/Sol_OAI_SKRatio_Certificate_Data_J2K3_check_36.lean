-- Prove2me | solution 1 for OAI.SKRatio.Certificate.Data.J2K3.check_36
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T23:12:28.570997+00:00
-- url     : https://prove2.me/submissions/081680ae-87a7-4f29-b691-b9a9e02b93be

import Mathlib
import Definitions.Def_OAIQ024S016

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ2K3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J2K3

lemma check_36_oai : expression.check (-10+(36:ℚ)*(5*(1/10))) (1/10) 5 (blocks 36) = true := by decide +kernel

end SKRatio.Certificate.Data.J2K3

end

end OAI
end

theorem solution : type_of% @OAI.SKRatio.Certificate.Data.J2K3.check_36_oai := @OAI.SKRatio.Certificate.Data.J2K3.check_36_oai
