-- Prove2me | solution 1 for OAI.ArExplicit.CocycleData.valid_true_f
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T13:49:48.88583+00:00
-- url     : https://prove2.me/submissions/aa3490c4-e035-47b6-90fd-aa509a65e7a4

import Mathlib
import Definitions.Def_OAIQ031A000

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cocycles_CocycleCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.CocycleData

private theorem valid_true_f_oai : certificate (true, .f) = true := by decide +kernel

end ArExplicit.CocycleData

end OAI
end

theorem solution : type_of% @OAI.ArExplicit.CocycleData.valid_true_f_oai := @OAI.ArExplicit.CocycleData.valid_true_f_oai
