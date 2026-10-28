-- Prove2me | solution 1 for OAI.ArExplicit.CocycleData.valid_true_y
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T13:52:48.722335+00:00
-- url     : https://prove2.me/submissions/6c6b52c0-2089-4a41-8542-3a46ccaefa16

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

private theorem valid_true_y_oai : certificate (true, .y) = true := by decide +kernel

end ArExplicit.CocycleData

end OAI
end

theorem solution : type_of% @OAI.ArExplicit.CocycleData.valid_true_y_oai := @OAI.ArExplicit.CocycleData.valid_true_y_oai
