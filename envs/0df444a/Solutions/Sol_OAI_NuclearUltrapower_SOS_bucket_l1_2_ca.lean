-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_l1_2_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T08:11:21.446186+00:00
-- url     : https://prove2.me/submissions/34bedf4f-a951-42c9-93d2-7c376718a9db

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
theorem bucket_l1_2_ca_oai : intL1 (residualBucket 2) = 106705360 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_l1_2_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_l1_2_ca_oai
