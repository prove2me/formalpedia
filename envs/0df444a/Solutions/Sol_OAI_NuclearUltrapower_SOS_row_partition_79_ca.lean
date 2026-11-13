-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_partition_79_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T22:31:51.140209+00:00
-- url     : https://prove2.me/submissions/538a4e17-7ec3-4958-9fe0-43c6c01342e7

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
theorem row_partition_79_ca_oai : normalize matLe residualRow79 = normalize matLe rowBuckets79.flatten := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_partition_79_ca_oai := @OAI.NuclearUltrapower.SOS.row_partition_79_ca_oai
