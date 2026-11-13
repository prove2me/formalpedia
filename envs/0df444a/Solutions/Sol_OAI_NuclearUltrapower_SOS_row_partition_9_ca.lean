-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_partition_9_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T22:51:38.621195+00:00
-- url     : https://prove2.me/submissions/42df8e1d-d808-40ab-98c0-d18f909d8b51

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
theorem row_partition_9_ca_oai : normalize matLe residualRow9 = normalize matLe rowBuckets9.flatten := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_partition_9_ca_oai := @OAI.NuclearUltrapower.SOS.row_partition_9_ca_oai
