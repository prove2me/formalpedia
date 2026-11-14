-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_l1_7_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T08:50:22.783993+00:00
-- url     : https://prove2.me/submissions/d3c64de6-ced3-4aed-a8e6-d0b00022178e

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
theorem bucket_l1_7_ca_oai : intL1 (residualBucket 7) = 252903380 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_l1_7_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_l1_7_ca_oai
