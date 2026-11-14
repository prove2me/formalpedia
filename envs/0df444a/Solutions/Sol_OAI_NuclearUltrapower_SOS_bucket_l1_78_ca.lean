-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_l1_78_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T09:04:25.674702+00:00
-- url     : https://prove2.me/submissions/269f6610-6dce-444f-811b-3ad839950433

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
theorem bucket_l1_78_ca_oai : intL1 (residualBucket 78) = 145650370 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_l1_78_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_l1_78_ca_oai
