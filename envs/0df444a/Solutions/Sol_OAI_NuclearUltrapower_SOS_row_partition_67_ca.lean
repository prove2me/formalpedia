-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_partition_67_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T19:28:24.210521+00:00
-- url     : https://prove2.me/submissions/80756c8b-c7cd-424f-b5bc-1a6ffe86a313

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
theorem row_partition_67_ca_oai : normalize matLe residualRow67 = normalize matLe rowBuckets67.flatten := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_partition_67_ca_oai := @OAI.NuclearUltrapower.SOS.row_partition_67_ca_oai
