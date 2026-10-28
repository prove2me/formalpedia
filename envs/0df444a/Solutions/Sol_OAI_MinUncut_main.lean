-- Prove2me | solution 1 for OAI.MinUncut.main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:00:31.643988+00:00
-- url     : https://prove2.me/submissions/41312252-a76d-44d9-b599-d490f2d3c275

import Mathlib
import Definitions.Def_MinUncut
import Definitions.Def_OAIQ076M031

section
-- module Solutions.OAIQ076_MU.MinUncut_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MinUncut

theorem main_oai : Nonempty Reduction := ⟨Uniform.reduction⟩
end MinUncut

end
end

end OAI
end

theorem solution : type_of% @OAI.MinUncut.main_oai := @OAI.MinUncut.main_oai
