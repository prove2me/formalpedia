-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.ElementarySpectral.deltaOp_certificate
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T17:13:28.182866+00:00
-- url     : https://prove2.me/submissions/be017628-7360-40cd-a8ab-8ccb0914f47c

import Mathlib
import Definitions.Def_OAIQ019N044
import Theorems.Thm_OAI_NuclearUltrapower_SOS_ElementarySpectral_operator_certificate
import Theorems.Thm_OAI_NuclearUltrapower_SOS_ElementarySpectral_residualInE_operator
import Theorems.Thm_OAI_NuclearUltrapower_SOS_ElementarySpectral_residual_value_native

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_IntegralCertificate
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instSeminormedRingPoly _root_.OAI.NuclearUltrapower.CuntzWords.instDecidableEqWord _root_.OAI.NuclearUltrapower.CuntzWords.instFintypeWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.VariableUltra.instCStarAlgebraAlgebra _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
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

attribute [local irreducible] gramValue eval residual

theorem deltaOp_certificate_oai (ρ : E →* (H ≃ₗᵢ[ℂ] H)) :
    (10000000000000 : ℝ) • (deltaOp ρ * deltaOp ρ) - (1000000000000 : ℝ) • deltaOp ρ =
      gramOp ρ + SOSEnergy.polyOperator ρ residualInE := by
  rw [residualInE_operator]
  exact operator_certificate
    (eval (value (A := H →L[ℂ] H) (unitaryRep ρ)) delta)
    (gramValue (value (A := H →L[ℂ] H) (unitaryRep ρ)))
    (eval (value (A := H →L[ℂ] H) (unitaryRep ρ)) residual)
    (residual_value_native ρ)

end Hilbert
end NuclearUltrapower.SOS.ElementarySpectral
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.NuclearUltrapower.SOS.ElementarySpectral.deltaOp_certificate_oai.{u_1} := @OAI.NuclearUltrapower.SOS.ElementarySpectral.deltaOp_certificate_oai.{u_1}
