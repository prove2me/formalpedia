-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.augmentation_flatten
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T13:02:49.341328+00:00
-- url     : https://prove2.me/submissions/f7a805c7-1cb2-44d5-8638-7ebddc0ffe56

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

theorem augmentation_flatten_oai {α : Type*} (rs : List (Poly α)) :
    augmentation rs.flatten = (rs.map augmentation).sum := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [augmentation, List.map_append, List.sum_append, List.flatten_cons, List.map_cons, List.sum_cons] at *
    exact congrArg (fun t : ℤ => augmentation r + t) ih

end NuclearUltrapower.SOS
end

end OAI
end

theorem solution.{u_2} : type_of% @OAI.NuclearUltrapower.SOS.augmentation_flatten_oai.{u_2} := @OAI.NuclearUltrapower.SOS.augmentation_flatten_oai.{u_2}
