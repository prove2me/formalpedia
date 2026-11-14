-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_l1_127_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T08:04:51.555312+00:00
-- url     : https://prove2.me/submissions/c95f8b34-0c51-4d9f-abb6-999d3cb0e0d3

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
theorem bucket_l1_127_ca_oai : intL1 (residualBucket 127) = 422209180 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_l1_127_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_l1_127_ca_oai
