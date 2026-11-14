-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_partition_66_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T12:12:44.668281+00:00
-- url     : https://prove2.me/submissions/c32fa54e-76a8-4a14-a7a6-93aae1eddf54

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
theorem row_partition_66_ca_oai : normalize matLe residualRow66 = normalize matLe rowBuckets66.flatten := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_partition_66_ca_oai := @OAI.NuclearUltrapower.SOS.row_partition_66_ca_oai
