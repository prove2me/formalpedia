-- Prove2me | solution 1 for OAI.ArExplicit.CocycleData.valid_true_n
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T13:50:12.974051+00:00
-- url     : https://prove2.me/submissions/7d4f6c8e-1ed7-4f00-a86d-c8bbf8c381a6

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

private theorem valid_true_n_oai : certificate (true, .n) = true := by decide +kernel

end ArExplicit.CocycleData

end OAI
end

theorem solution : type_of% @OAI.ArExplicit.CocycleData.valid_true_n_oai := @OAI.ArExplicit.CocycleData.valid_true_n_oai
