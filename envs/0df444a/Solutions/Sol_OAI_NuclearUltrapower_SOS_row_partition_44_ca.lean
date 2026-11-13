-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_partition_44_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T16:34:49.262425+00:00
-- url     : https://prove2.me/submissions/f4379d4e-081c-4ad8-ba09-70181036bb80

import Mathlib
import Definitions.Def_OAIQ229C015
import Definitions.Def_OAIQ229C021

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
theorem row_partition_44_ca_oai : normalize matLe residualRow44 = normalize matLe rowBuckets44.flatten := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_partition_44_ca_oai := @OAI.NuclearUltrapower.SOS.row_partition_44_ca_oai
