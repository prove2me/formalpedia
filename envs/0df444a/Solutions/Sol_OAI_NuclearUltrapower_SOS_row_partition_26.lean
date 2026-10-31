-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_partition_26
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T13:58:00.433862+00:00
-- url     : https://prove2.me/submissions/690fb2b4-1fc8-41c1-be89-7523642ba472

import Mathlib
import Definitions.Def_OAIQ019N048
import Definitions.Def_OAIQ019N043

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_SOSResidual
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzWords.instDecidableEqWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SOS
theorem row_partition_26_oai : normalize matLe residualRow26 = normalize matLe rowBuckets26.flatten := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_partition_26_oai := @OAI.NuclearUltrapower.SOS.row_partition_26_oai
