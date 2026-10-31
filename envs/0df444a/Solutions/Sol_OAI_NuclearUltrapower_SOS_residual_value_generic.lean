-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.residual_value_generic
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T17:29:41.634481+00:00
-- url     : https://prove2.me/submissions/a7bd9759-4086-4d5f-bb29-9e9a6bab7699

import Mathlib
import Definitions.Def_OAIQ019N044
import Theorems.Thm_OAI_NuclearUltrapower_SOS_eval_gram_rows
import Theorems.Thm_OAI_NuclearUltrapower_SOS_eval_mul
import Theorems.Thm_OAI_NuclearUltrapower_SOS_eval_scale
import Theorems.Thm_OAI_NuclearUltrapower_SOS_residual_eval

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_IntegralCertificate
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarPoly _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarWord _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarPoly _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.VariableUltra.instStarAlgebra _root_.OAI.NuclearUltrapower.instStarNormUltrapower _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SOS
open NuclearUltrapower.SL3Certificate

theorem residualRows_decomp : residualRows = residualRow0 :: residualRow1 ::
    (basis.zip gramData).map (fun p => gramPolyRow p.1 p.2) := by rfl

end NuclearUltrapower.SOS
end

section
noncomputable section
namespace NuclearUltrapower.SOS
section
variable {A : Type*} [Ring A] [StarRing A]
theorem residual_value_generic_oai (f : Mat3 → A)
    (hf : ∀ a ∈ delta.map Prod.fst, ∀ b ∈ delta.map Prod.fst,
      f (matMul a b) = f a * f b)
    (hg : ∀ a ∈ basis, ∀ b ∈ basis,
      f (matMul (matInv a) b) = star (f a) * f b) :
    eval f residual = (10000000000000 : ℤ) • (eval f delta * eval f delta) -
      (1000000000000 : ℤ) • eval f delta - (10 : ℤ) • gramValue f := by
  rw [residual_eval, residualRows_decomp]
  simp only [List.flatten_cons, eval_append]
  rw [residualRow0, eval_scale, residualRow1, eval_scale]
  have hm : eval f (polyMul delta delta) = eval f delta * eval f delta := by
    apply eval_mul
    intro p hp q hq
    exact hf p.1 (List.mem_map_of_mem hp) q.1 (List.mem_map_of_mem hq)
  rw [hm]
  rw [← List.flatMap_def, eval_gram_rows f hg]
  simp only [neg_smul, sub_eq_add_neg]
  rw [add_assoc]
end
end NuclearUltrapower.SOS
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.NuclearUltrapower.SOS.residual_value_generic_oai.{u_1} := @OAI.NuclearUltrapower.SOS.residual_value_generic_oai.{u_1}
