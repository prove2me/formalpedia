-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_aug_74
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T15:22:50.571787+00:00
-- url     : https://prove2.me/submissions/a92cac9d-2afb-47f2-ae72-a07ac484c7a5

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
theorem bucket_aug_74_oai : ((residualBucket 74).map Prod.snd).sum = -23785340 := by decide +kernel
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.bucket_aug_74_oai := @OAI.NuclearUltrapower.SOS.bucket_aug_74_oai
