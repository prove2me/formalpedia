-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.support_normalize_iff
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T13:07:22.12103+00:00
-- url     : https://prove2.me/submissions/f993eab8-b27e-442c-a5e2-389ad9ff6811

import Mathlib
import Definitions.Def_OAIQ019N047
import Theorems.Thm_OAI_NuclearUltrapower_SOS_support_compress_iff

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_SOSSemantics
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzWords.instDecidableEqWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SOS
variable {α A : Type*} [DecidableEq α]

theorem support_normalize_iff_oai (le : α → α → Bool) (ps : Poly α) (g : α) :
    g ∈ (normalize le ps).map Prod.fst ↔ g ∈ ps.map Prod.fst := by
  rw [normalize, support_compress_iff]
  exact ((List.perm_insertionSort _ ps).map Prod.fst).mem_iff

end NuclearUltrapower.SOS

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.NuclearUltrapower.SOS.support_normalize_iff_oai.{u_1} := @OAI.NuclearUltrapower.SOS.support_normalize_iff_oai.{u_1}
