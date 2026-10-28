-- Prove2me | solution 1 for OAI.ArExplicit.CocycleData.valid_true_t
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T13:50:14.31324+00:00
-- url     : https://prove2.me/submissions/9688b848-048f-45b4-a82a-8fb5cdab9e7f

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

private theorem valid_true_t_oai : certificate (true, .t) = true := by decide +kernel

end ArExplicit.CocycleData

end OAI
end

theorem solution : type_of% @OAI.ArExplicit.CocycleData.valid_true_t_oai := @OAI.ArExplicit.CocycleData.valid_true_t_oai
