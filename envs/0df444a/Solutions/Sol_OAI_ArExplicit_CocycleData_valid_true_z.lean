-- Prove2me | solution 1 for OAI.ArExplicit.CocycleData.valid_true_z
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T13:53:53.624635+00:00
-- url     : https://prove2.me/submissions/4574118d-0863-4666-80d4-5d82c1564c5d

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

private theorem valid_true_z_oai : certificate (true, .z) = true := by decide +kernel

end ArExplicit.CocycleData

end OAI
end

theorem solution : type_of% @OAI.ArExplicit.CocycleData.valid_true_z_oai := @OAI.ArExplicit.CocycleData.valid_true_z_oai
