-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.intL1_flatten
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T13:04:36.182978+00:00
-- url     : https://prove2.me/submissions/eac04d83-59b4-4180-a736-4b35c875b695

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
variable {A : Type*} [AddCommGroup A]

theorem intL1_flatten_oai {α : Type*} (rs : List (Poly α)) :
    intL1 rs.flatten = (rs.map intL1).sum := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [intL1, List.map_append, List.sum_append, List.flatten_cons, List.map_cons, List.sum_cons] at *
    exact congrArg (fun t : ℤ => intL1 r + t) ih

end NuclearUltrapower.SOS
end

end OAI
end

theorem solution.{u_2} : type_of% @OAI.NuclearUltrapower.SOS.intL1_flatten_oai.{u_2} := @OAI.NuclearUltrapower.SOS.intL1_flatten_oai.{u_2}
