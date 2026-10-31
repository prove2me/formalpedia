-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.support_addHead_iff
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T13:06:33.276108+00:00
-- url     : https://prove2.me/submissions/a0acf7c0-99f2-46ba-8fec-560a0ba4f9fa

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

theorem support_addHead_iff_oai (p : α × ℤ) (ps : Poly α) (g : α) :
    g ∈ (addHead p ps).map Prod.fst ↔ g = p.1 ∨ g ∈ ps.map Prod.fst := by
  cases ps with
  | nil => simp [addHead]
  | cons q qs =>
    simp only [addHead]
    split_ifs with h <;> simp_all

end NuclearUltrapower.SOS

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.NuclearUltrapower.SOS.support_addHead_iff_oai.{u_1} := @OAI.NuclearUltrapower.SOS.support_addHead_iff_oai.{u_1}
