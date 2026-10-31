-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.eval_scale
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T12:58:49.1005+00:00
-- url     : https://prove2.me/submissions/15c4f15a-d4bc-40f9-8213-88f65092c662

import Mathlib
import Definitions.Def_OAIQ019N047

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_SOSSemantics
attribute [-instance] _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SOS
variable {α A : Type*} [DecidableEq α]

section EvalOperations
variable [Ring A]
omit [DecidableEq α] in
theorem eval_scale_oai (f : α → A) (ps : Poly α) (k : ℤ) :
    eval f (ps.map (fun p => (p.1, k*p.2))) = k • eval f ps := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    simp only [List.map_cons, eval_cons, smul_add, ih, mul_smul]

end EvalOperations
end NuclearUltrapower.SOS

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.NuclearUltrapower.SOS.eval_scale_oai.{u_1, u_2} := @OAI.NuclearUltrapower.SOS.eval_scale_oai.{u_1, u_2}
