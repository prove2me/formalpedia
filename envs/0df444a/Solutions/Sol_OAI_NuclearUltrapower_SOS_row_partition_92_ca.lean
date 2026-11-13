-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_partition_92_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T01:12:25.546211+00:00
-- url     : https://prove2.me/submissions/87a52033-d901-4c85-aa60-c05ef5df08ef

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
theorem row_partition_92_ca_oai : normalize matLe residualRow92 = normalize matLe rowBuckets92.flatten := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_partition_92_ca_oai := @OAI.NuclearUltrapower.SOS.row_partition_92_ca_oai
