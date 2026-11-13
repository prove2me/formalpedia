-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_partition_78_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T23:26:53.645181+00:00
-- url     : https://prove2.me/submissions/e2d4f669-7e58-4efa-aa15-0e458f506a64

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
theorem row_partition_78_ca_oai : normalize matLe residualRow78 = normalize matLe rowBuckets78.flatten := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_partition_78_ca_oai := @OAI.NuclearUltrapower.SOS.row_partition_78_ca_oai
