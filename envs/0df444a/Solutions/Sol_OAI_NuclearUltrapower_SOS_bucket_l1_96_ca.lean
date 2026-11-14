-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_l1_96_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T10:02:57.193588+00:00
-- url     : https://prove2.me/submissions/a8df2e20-4503-4edf-adb3-e468b7ba27fd

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
theorem bucket_l1_96_ca_oai : intL1 (residualBucket 96) = 161533820 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_l1_96_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_l1_96_ca_oai
