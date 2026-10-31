-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.interpret_mul
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T13:11:37.43384+00:00
-- url     : https://prove2.me/submissions/e4710759-68f7-4b80-b4d0-2dcd0292e928

import Mathlib
import Definitions.Def_OAIQ019N048
import Theorems.Thm_OAI_NuclearUltrapower_SOS_interpret_coe
import Theorems.Thm_OAI_NuclearUltrapower_SOS_toMatrix_mul

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_SOSSemantics
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzWords.instDecidableEqWord _root_.OAI.NuclearUltrapower.CuntzWords.instFintypeWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SOS

theorem interpret_mul_oai (a b : Mat3) (ha : (toMatrix a).det = 1) (hb : (toMatrix b).det = 1) :
    interpret (matMul a b) = interpret a * interpret b := by
  apply Subtype.ext
  rw [interpret_coe _ (by rw [toMatrix_mul, Matrix.det_mul, ha, hb, one_mul]),
    Matrix.SpecialLinearGroup.coe_mul, interpret_coe _ ha, interpret_coe _ hb, toMatrix_mul]

end NuclearUltrapower.SOS

end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.interpret_mul_oai := @OAI.NuclearUltrapower.SOS.interpret_mul_oai
