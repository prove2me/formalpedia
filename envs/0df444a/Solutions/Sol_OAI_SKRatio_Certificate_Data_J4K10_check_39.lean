-- Prove2me | solution 1 for OAI.SKRatio.Certificate.Data.J4K10.check_39
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T00:01:14.612934+00:00
-- url     : https://prove2.me/submissions/6e4e62ce-6c82-4985-9307-0cba1b069a21

import Mathlib
import Definitions.Def_OAIQ024S016

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_ScalarDataJ4K10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate.Data.J4K10

lemma check_39_oai : expression.check (-10+(39:ℚ)*(10*(1/20))) (1/20) 10 (blocks 39) = true := by decide +kernel

end SKRatio.Certificate.Data.J4K10

end

end OAI
end

theorem solution : type_of% @OAI.SKRatio.Certificate.Data.J4K10.check_39_oai := @OAI.SKRatio.Certificate.Data.J4K10.check_39_oai
