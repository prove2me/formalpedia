-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.eval_gram_rows
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T17:27:05.603692+00:00
-- url     : https://prove2.me/submissions/5f3364cb-ae02-46e1-bcc9-e85bc537b5d4

import Mathlib
import Definitions.Def_OAIQ019N044
import Theorems.Thm_OAI_NuclearUltrapower_SOS_gramData_roots

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

section Operator
variable {A : Type*} [Ring A] [StarRing A]

theorem eval_gram_rows_oai (f : Mat3 → A)
    (hf : ∀ a ∈ basis, ∀ b ∈ basis,
      f (matMul (matInv a) b) = star (f a) * f b) :
    eval f ((basis.zip gramData).flatMap (fun p => gramPolyRow p.1 p.2)) =
      (-10 : ℤ) • gramValue f := by
  rw [gramData_roots]
  simp only [List.zip_map_right, List.flatMap_map, Prod.map, id_eq,
    Function.comp_def, gramPolyRow, List.map_map]
  rw [eval_flatMap]
  have hrow (p : Mat3 × List ℤ) (hp : p ∈ rootPairs) :
      eval f ((basis.zip columns).map (fun q =>
        (matMul (matInv p.1) q.1, -10 * dot p.2 q.2))) =
        (-10 : ℤ) • (rootPairs.map (fun q => dot p.2 q.2 • (star (f p.1) * f q.1))).sum := by
    simp only [eval, List.map_map, Function.comp_def, mul_smul, List.smul_sum,
      List.map_map]
    congr 1
    apply List.map_congr_left
    intro q hq
    rw [hf p.1 (List.of_mem_zip hp).1 q.1 (List.of_mem_zip hq).1]
  change (rootPairs.map (fun p => eval f ((basis.zip columns).map
    (fun q => (matMul (matInv p.1) q.1, -10 * dot p.2 q.2))))).sum = _
  rw [List.map_congr_left hrow]
  simp only [gramValue, List.smul_sum, List.map_map, Function.comp_def]

end Operator
end NuclearUltrapower.SOS
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.NuclearUltrapower.SOS.eval_gram_rows_oai.{u_1} := @OAI.NuclearUltrapower.SOS.eval_gram_rows_oai.{u_1}
