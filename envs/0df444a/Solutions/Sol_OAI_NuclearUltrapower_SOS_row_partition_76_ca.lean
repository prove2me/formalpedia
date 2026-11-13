-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_partition_76_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T23:21:58.794386+00:00
-- url     : https://prove2.me/submissions/a3d14423-f145-4c74-b2df-05d7a3025ec7

import Mathlib
import Definitions.Def_OAIQ229C022

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
theorem row_partition_76_ca_oai : normalize matLe residualRow76 = normalize matLe rowBuckets76.flatten := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_partition_76_ca_oai := @OAI.NuclearUltrapower.SOS.row_partition_76_ca_oai
