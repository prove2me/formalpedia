-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.residual_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T17:27:52.320314+00:00
-- url     : https://prove2.me/submissions/8b45b7bc-ea14-4d52-9fde-c0bbaffb14a6

import Mathlib
import Definitions.Def_OAIQ019N044
import Theorems.Thm_OAI_NuclearUltrapower_SOS_eval_buckets
import Theorems.Thm_OAI_NuclearUltrapower_SOS_eval_normalize
import Theorems.Thm_OAI_NuclearUltrapower_SOS_row_length_bound
import Theorems.Thm_OAI_NuclearUltrapower_SOS_row_normalizations

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_SOSSemantics
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzWords.instDecidableEqWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SOS
variable {A : Type*} [AddCommGroup A]

theorem residual_eval_oai (f : Mat3 → A) : eval f residual = eval f residualRows.flatten := by
  change eval f ((List.range 128).flatMap residualBucket) = _
  unfold residualBucket
  rw [eval_buckets 128 allRowBuckets row_length_bound]
  have he := congrArg (fun ps : List (Poly Mat3) => (ps.map (eval f)).sum) row_normalizations
  simp only [List.map_map, Function.comp_def, eval_normalize] at he
  simpa only [eval_flatMap, eval_flatten] using he.symm

end NuclearUltrapower.SOS
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.NuclearUltrapower.SOS.residual_eval_oai.{u_1} := @OAI.NuclearUltrapower.SOS.residual_eval_oai.{u_1}
