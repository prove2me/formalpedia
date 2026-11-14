-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_partition_84_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T12:03:40.163995+00:00
-- url     : https://prove2.me/submissions/89b8263e-f0cd-4d8e-b01e-66a11de3afdb

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
theorem row_partition_84_ca_oai : normalize matLe residualRow84 = normalize matLe rowBuckets84.flatten := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_partition_84_ca_oai := @OAI.NuclearUltrapower.SOS.row_partition_84_ca_oai
