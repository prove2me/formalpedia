-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_partition_75_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T00:13:18.303873+00:00
-- url     : https://prove2.me/submissions/32ce021e-739e-4d28-9096-5d13910085d0

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
theorem row_partition_75_ca_oai : normalize matLe residualRow75 = normalize matLe rowBuckets75.flatten := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_partition_75_ca_oai := @OAI.NuclearUltrapower.SOS.row_partition_75_ca_oai
