-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_partition_71_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T21:36:37.521307+00:00
-- url     : https://prove2.me/submissions/94bb76fb-6da3-4973-9eb9-10393374b754

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
theorem row_partition_71_ca_oai : normalize matLe residualRow71 = normalize matLe rowBuckets71.flatten := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_partition_71_ca_oai := @OAI.NuclearUltrapower.SOS.row_partition_71_ca_oai
