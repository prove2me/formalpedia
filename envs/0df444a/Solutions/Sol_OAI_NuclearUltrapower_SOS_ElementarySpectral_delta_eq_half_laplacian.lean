-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.ElementarySpectral.delta_eq_half_laplacian
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T17:18:10.827145+00:00
-- url     : https://prove2.me/submissions/ec83f982-14b0-4b76-8f48-906fea7d7dbc

import Mathlib
import Definitions.Def_OAIQ019N044
import Theorems.Thm_OAI_NuclearUltrapower_SOS_ElementarySpectral_delta_value
import Theorems.Thm_OAI_NuclearUltrapower_SOS_ElementarySpectral_genList_nodup
import Theorems.Thm_OAI_NuclearUltrapower_SOS_ElementarySpectral_sum_gen_star

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_SOSGap
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarPoly _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarWord _root_.OAI.NuclearUltrapower.CuntzPolynomial.instSeminormedRingPoly _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarPoly _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord _root_.OAI.NuclearUltrapower.CuntzWords.instDecidableEqWord _root_.OAI.NuclearUltrapower.CuntzWords.instFintypeWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAlgebraComplexAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedRingAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instStarAlgebra _root_.OAI.NuclearUltrapower.instStarNormUltrapower _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped ComplexOrder InnerProductSpace
namespace NuclearUltrapower.SOS.ElementarySpectral

theorem eGenSet_card : eGenSet.card = 12 := by
  rw [eGenSet, List.toFinset_card_of_nodup genList_nodup]
  rfl

section Algebra
variable {A : Type*} [CStarAlgebra A]

theorem laplacian_eq_delta (ρ : E →* unitary A) :
    laplacian eGenSet (fun g => (ρ g : A)) = (2 : ℝ) • eval (value ρ) delta := by
  have h (g : E) : star ((ρ g : A) - 1) * ((ρ g : A) - 1) =
      1 - star (ρ g : A) - (ρ g : A) + 1 := by
    simp only [star_sub, star_one, sub_mul, mul_sub, Unitary.coe_star_mul_self,
      one_mul, mul_one]
    abel
  simp only [laplacian, h, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    sum_gen_star, Finset.sum_const, eGenSet_card, delta_value]
  module

theorem delta_eq_half_laplacian_oai (ρ : E →* unitary A) :
    eval (value ρ) delta = (1/2 : ℝ) • laplacian eGenSet (fun g => (ρ g : A)) := by
  rw [laplacian_eq_delta, smul_smul]
  norm_num

end Algebra

end NuclearUltrapower.SOS.ElementarySpectral
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.NuclearUltrapower.SOS.ElementarySpectral.delta_eq_half_laplacian_oai.{u_1} := @OAI.NuclearUltrapower.SOS.ElementarySpectral.delta_eq_half_laplacian_oai.{u_1}
