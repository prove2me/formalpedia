-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.row_length_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T16:40:10.766825+00:00
-- url     : https://prove2.me/submissions/db600931-3827-4336-8b25-cf0f7243d83d

import Mathlib
import Definitions.Def_OAIQ019N049
import Theorems.Thm_OAI_NuclearUltrapower_SOS_row_lengths

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

theorem row_length_bound_oai : ∀ r ∈ allRowBuckets, r.length ≤ 128 := by
  intro r hr
  have h := List.mem_map_of_mem (f := List.length) hr
  rw [row_lengths] at h
  have : r.length = 128 := (List.mem_replicate.mp h).2
  omega

end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.row_length_bound_oai := @OAI.NuclearUltrapower.SOS.row_length_bound_oai
