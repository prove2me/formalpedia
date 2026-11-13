-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_partition_29_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T15:53:40.107664+00:00
-- url     : https://prove2.me/submissions/b7efed16-58d4-4ee8-9470-d1985a8c14a6

import Mathlib
import Definitions.Def_OAIQ229C015
import Definitions.Def_OAIQ229C021

section
-- module Solutions.Q229_CA.NuclearUltrapower_SOSResidual
attribute [-instance] _root_.OAI.CoarseAssembly.baseUnionDecidableEq _root_.OAI.CoarseAssembly.vertexUnionDecidableEq _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SOS
theorem row_partition_29_ca_oai : normalize matLe residualRow29 = normalize matLe rowBuckets29.flatten := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_partition_29_ca_oai := @OAI.NuclearUltrapower.SOS.row_partition_29_ca_oai
