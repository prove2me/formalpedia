-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.ElementarySpectral.deltaOp_sq_gap
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T17:15:39.20153+00:00
-- url     : https://prove2.me/submissions/b5e7a14e-c23a-4bdf-97f7-c6c3c83b0f9f

import Mathlib
import Definitions.Def_OAIQ019N044
import Theorems.Thm_OAI_NuclearUltrapower_SOS_ElementarySpectral_deltaOp_certificate
import Theorems.Thm_OAI_NuclearUltrapower_SOS_ElementarySpectral_deltaOp_nonneg
import Theorems.Thm_OAI_NuclearUltrapower_SOS_ElementarySpectral_delta_energy
import Theorems.Thm_OAI_NuclearUltrapower_SOS_ElementarySpectral_gramOp_nonneg
import Theorems.Thm_OAI_NuclearUltrapower_SOS_ElementarySpectral_residualInE_aug
import Theorems.Thm_OAI_NuclearUltrapower_SOS_ElementarySpectral_residualInE_l1
import Theorems.Thm_OAI_NuclearUltrapower_SOS_ElementarySpectral_residualInE_support
import Theorems.Thm_OAI_NuclearUltrapower_SOSEnergy_certificate_sq_gap

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_IntegralCertificate
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instSeminormedRingPoly _root_.OAI.NuclearUltrapower.CuntzWords.instDecidableEqWord _root_.OAI.NuclearUltrapower.CuntzWords.instFintypeWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
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

theorem deltaOp_energy (ρ : E →* (H ≃ₗᵢ[ℂ] H)) (x : H) :
    (inner ℂ x (deltaOp ρ x)).re = SOSEnergy.energy eGenSet ρ x / 2 :=
  delta_energy ρ x

end Hilbert
end NuclearUltrapower.SOS.ElementarySpectral
end
end

section

noncomputable section
open scoped InnerProductSpace ComplexOrder
namespace NuclearUltrapower.SOS.ElementarySpectral
section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local irreducible] gramValue eval residual

theorem deltaOp_sq_gap_oai (ρ : E →* (H ≃ₗᵢ[ℂ] H)) :
    (1/20 : ℝ) • deltaOp ρ ≤ deltaOp ρ * deltaOp ρ :=
  SOSEnergy.certificate_sq_gap eGenSet ρ (deltaOp ρ) (gramOp ρ) residualInE
    (deltaOp_nonneg ρ) (gramOp_nonneg ρ) (deltaOp_energy ρ) residualInE_aug
    residualInE_l1 residualInE_support (deltaOp_certificate ρ)

end Hilbert
end NuclearUltrapower.SOS.ElementarySpectral
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.NuclearUltrapower.SOS.ElementarySpectral.deltaOp_sq_gap_oai.{u_1} := @OAI.NuclearUltrapower.SOS.ElementarySpectral.deltaOp_sq_gap_oai.{u_1}
