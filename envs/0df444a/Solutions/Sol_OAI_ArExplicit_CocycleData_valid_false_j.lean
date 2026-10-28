-- Prove2me | solution 1 for OAI.ArExplicit.CocycleData.valid_false_j
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T13:42:53.73698+00:00
-- url     : https://prove2.me/submissions/13c687ac-7a01-4acc-86a5-6746d6cc63e5

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

private theorem valid_false_j_oai : certificate (false, .j) = true := by decide +kernel

end ArExplicit.CocycleData

end OAI
end

theorem solution : type_of% @OAI.ArExplicit.CocycleData.valid_false_j_oai := @OAI.ArExplicit.CocycleData.valid_false_j_oai
