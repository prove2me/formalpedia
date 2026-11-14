-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_l1_76_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T09:23:18.938098+00:00
-- url     : https://prove2.me/submissions/22884546-5530-43d0-9dff-cb9a007639c4

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
theorem bucket_l1_76_ca_oai : intL1 (residualBucket 76) = 301019530 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_l1_76_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_l1_76_ca_oai
