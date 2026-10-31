-- Prove2me | solution 1 for OAI.NuclearUltrapower.CuntzAveraging.averaged_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T13:00:31.767988+00:00
-- url     : https://prove2.me/submissions/224a534d-585f-48be-bd35-d8200fb67e0a

import Mathlib
import Definitions.Def_OAIQ019N048
import Theorems.Thm_OAI_NuclearUltrapower_CuntzAveraging_averaged_norm

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_CuntzWords
attribute [-instance] _root_.OAI.NuclearUltrapower.VariableUltra.instCStarAlgebraAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAlgebraComplexAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedRingAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instStarAlgebra _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped TensorProduct InnerProductSpace
namespace NuclearUltrapower.CuntzAveraging
open CuntzModel CuntzWords CuntzUniversal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (R : Algebra →⋆ₙₐ[ℂ] (H →L[ℂ] H))

theorem support_norm_le (x : H) : ‖R 1 x‖ ≤ ‖x‖ := by
  have hR : ‖R 1‖ ≤ 1 := by simpa only [norm_one] using NonUnitalStarAlgHom.norm_apply_le R (1 : Algebra)
  simpa only [one_mul] using (R 1).le_of_opNorm_le hR x

end NuclearUltrapower.CuntzAveraging
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_CuntzIntertwining
attribute [-instance] _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAddCommGroupAlgebra _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Filter
open scoped TensorProduct InnerProductSpace Topology
namespace NuclearUltrapower.CuntzAveraging
open CuntzModel CuntzWords CuntzUniversal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (R : Algebra →⋆ₙₐ[ℂ] (H →L[ℂ] H))

theorem averaged_norm_le_oai (n : ℕ) : ‖averaged R n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul,averaged_norm]
  exact support_norm_le R x

end NuclearUltrapower.CuntzAveraging
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.NuclearUltrapower.CuntzAveraging.averaged_norm_le_oai.{u_1} := @OAI.NuclearUltrapower.CuntzAveraging.averaged_norm_le_oai.{u_1}
