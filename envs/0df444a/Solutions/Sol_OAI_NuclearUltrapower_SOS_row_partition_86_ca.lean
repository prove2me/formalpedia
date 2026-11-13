-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_partition_86_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T23:25:46.827176+00:00
-- url     : https://prove2.me/submissions/90f417f9-f2d5-45d6-87bc-53cecebcb05b

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
theorem row_partition_86_ca_oai : normalize matLe residualRow86 = normalize matLe rowBuckets86.flatten := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_partition_86_ca_oai := @OAI.NuclearUltrapower.SOS.row_partition_86_ca_oai
