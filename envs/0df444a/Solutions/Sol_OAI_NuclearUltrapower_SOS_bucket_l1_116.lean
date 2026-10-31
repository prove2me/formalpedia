-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_l1_116
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T15:44:15.05984+00:00
-- url     : https://prove2.me/submissions/08ea392b-c77c-4737-ad50-585e6e833496

import Mathlib
import Definitions.Def_OAIQ019N049

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_SOSResidual
attribute [-instance] _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SOS
theorem bucket_l1_116_oai : intL1 (residualBucket 116) = 283773650 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_l1_116_oai := @OAI.NuclearUltrapower.SOS.bucket_l1_116_oai
