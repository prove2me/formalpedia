-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_l1_57_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T09:16:00.514962+00:00
-- url     : https://prove2.me/submissions/ad2f4d45-f0ff-4696-869b-22acafe83ee4

import Mathlib
import Definitions.Def_OAIQ229C027

section
-- module Solutions.Q229_CA.NuclearUltrapower_SOSResidual
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SOS
theorem bucket_l1_57_ca_oai : intL1 (residualBucket 57) = 204376700 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_l1_57_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_l1_57_ca_oai
