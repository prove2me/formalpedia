-- Prove2me | solution 1 for OAI.ArExplicit.CocycleData.valid_false_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T13:47:36.862802+00:00
-- url     : https://prove2.me/submissions/03a87520-78f2-4258-867e-f1e1a4f3575a

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

private theorem valid_false_x_oai : certificate (false, .x) = true := by decide +kernel

end ArExplicit.CocycleData

end OAI
end

theorem solution : type_of% @OAI.ArExplicit.CocycleData.valid_false_x_oai := @OAI.ArExplicit.CocycleData.valid_false_x_oai
