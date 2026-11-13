-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_partition_65_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T20:46:05.148929+00:00
-- url     : https://prove2.me/submissions/59fa2a0f-942b-4762-99c6-c29a2f90ab0e

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
theorem row_partition_65_ca_oai : normalize matLe residualRow65 = normalize matLe rowBuckets65.flatten := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_partition_65_ca_oai := @OAI.NuclearUltrapower.SOS.row_partition_65_ca_oai
