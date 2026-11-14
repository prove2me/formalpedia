-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_l1_98_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T09:53:10.718029+00:00
-- url     : https://prove2.me/submissions/3c9bc90b-c491-4c61-8a12-8a61409b817a

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
theorem bucket_l1_98_ca_oai : intL1 (residualBucket 98) = 169270620 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_l1_98_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_l1_98_ca_oai
