-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.ElementarySpectral.residualInE_operator
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T17:22:59.564861+00:00
-- url     : https://prove2.me/submissions/ba9c1d1f-5d94-4ee1-87c1-820a07146c24

import Mathlib
import Definitions.Def_OAIQ019N044

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_IntegralCertificate
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzWords.instDecidableEqWord _root_.OAI.NuclearUltrapower.CuntzWords.instFintypeWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.VariableUltra.instCStarAlgebraAlgebra _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped InnerProductSpace ComplexOrder
namespace NuclearUltrapower.SOS.ElementarySpectral

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem residualInE_operator_oai (ρ : E →* (H ≃ₗᵢ[ℂ] H)) :
    SOSEnergy.polyOperator ρ residualInE =
      eval (value (A := H →L[ℂ] H) (unitaryRep ρ)) residual := by
  simp only [SOSEnergy.polyOperator, residualInE, eval, List.map_map, Function.comp_def,
    value, unitaryRep_coe]

end Hilbert
end NuclearUltrapower.SOS.ElementarySpectral
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.NuclearUltrapower.SOS.ElementarySpectral.residualInE_operator_oai.{u_1} := @OAI.NuclearUltrapower.SOS.ElementarySpectral.residualInE_operator_oai.{u_1}
