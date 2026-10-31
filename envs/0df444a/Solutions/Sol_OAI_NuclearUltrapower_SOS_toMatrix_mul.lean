-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.toMatrix_mul
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T13:07:47.302205+00:00
-- url     : https://prove2.me/submissions/9f66df69-9c54-47d0-8d1c-e692afb488bc

import Mathlib
import Definitions.Def_OAIQ019N039
import Definitions.Def_OAIQ019N047

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_SOSSemantics
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzWords.instFintypeWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SOS

theorem toMatrix_mul_oai (a b : Mat3) : toMatrix (matMul a b) = toMatrix a * toMatrix b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toMatrix, matMul, entry, Matrix.mul_apply, Fin.sum_univ_succ, List.range_succ, add_assoc]

end NuclearUltrapower.SOS

end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.toMatrix_mul_oai := @OAI.NuclearUltrapower.SOS.toMatrix_mul_oai
