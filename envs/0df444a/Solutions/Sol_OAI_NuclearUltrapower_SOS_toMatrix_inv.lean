-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.toMatrix_inv
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T13:07:46.018839+00:00
-- url     : https://prove2.me/submissions/df87854e-2293-4490-9c1a-7dcdf1a26f5d

import Mathlib
import Definitions.Def_OAIQ019N039
import Definitions.Def_OAIQ019N047

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

theorem toMatrix_inv_oai (a : Mat3) : toMatrix (matInv a) = (toMatrix a).adjugate := by
  rw [Matrix.adjugate_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toMatrix, matInv, entry, List.range_succ] <;> ring

end NuclearUltrapower.SOS

end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.toMatrix_inv_oai := @OAI.NuclearUltrapower.SOS.toMatrix_inv_oai
