-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.toMatrix_one
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T12:56:15.770056+00:00
-- url     : https://prove2.me/submissions/058a49cd-a1d7-40d6-8522-89840041ce7b

import Mathlib
import Definitions.Def_OAIQ019N039

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_SOSSemantics
attribute [-instance] _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.lp_finiteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SOS

theorem toMatrix_one_oai : toMatrix matOne = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

end NuclearUltrapower.SOS

end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.toMatrix_one_oai := @OAI.NuclearUltrapower.SOS.toMatrix_one_oai
