-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_partition_74_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T11:57:31.763351+00:00
-- url     : https://prove2.me/submissions/dc874203-1845-4233-a5b9-0485d7ddbb5b

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
theorem row_partition_74_ca_oai : normalize matLe residualRow74 = normalize matLe rowBuckets74.flatten := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_partition_74_ca_oai := @OAI.NuclearUltrapower.SOS.row_partition_74_ca_oai
