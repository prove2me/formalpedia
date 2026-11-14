-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_l1_59_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T09:14:32.252208+00:00
-- url     : https://prove2.me/submissions/171f4f6e-04fa-4b55-bb27-a2f8e7611bf5

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
theorem bucket_l1_59_ca_oai : intL1 (residualBucket 59) = 226438300 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_l1_59_ca_oai := @OAI.NuclearUltrapower.SOS.bucket_l1_59_ca_oai
