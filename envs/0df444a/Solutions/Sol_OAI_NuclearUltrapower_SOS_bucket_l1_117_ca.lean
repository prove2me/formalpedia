-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_l1_117_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:56:09.528239+00:00
-- url     : https://prove2.me/submissions/b1c1a050-4319-4183-9495-b2de2a188a5e

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
theorem bucket_l1_117_ca_oai : intL1 (residualBucket 117) = 208866020 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_l1_117_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_l1_117_ca_oai
