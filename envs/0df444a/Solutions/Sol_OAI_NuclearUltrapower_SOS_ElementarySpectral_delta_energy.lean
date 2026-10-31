-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.ElementarySpectral.delta_energy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T17:16:44.499912+00:00
-- url     : https://prove2.me/submissions/47e682cb-bf31-4a4f-92d5-eff9a8bb1606

import Mathlib
import Definitions.Def_OAIQ019N044
import Theorems.Thm_OAI_NuclearUltrapower_SOS_ElementarySpectral_delta_eq_half_laplacian

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_Laplacian
attribute [-instance] _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.VariableUltra.instCStarAlgebraAlgebra _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder
namespace NuclearUltrapower

section Operator
variable {Γ H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The quadratic form is exactly the energy, with no representation relations. -/
theorem laplacian_inner (S : Finset Γ) (u : Γ → (H →L[ℂ] H)) (x : H) :
    inner ℂ x (laplacian S u x) = (∑ s ∈ S, ‖u s x - x‖ ^ 2 : ℝ) := by
  simp only [laplacian, sum_apply, inner_sum, mul_apply_eq_comp,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  simp [inner_self_eq_norm_sq_to_K]

end Operator
end NuclearUltrapower
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_SOSGap
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzWords.instDecidableEqWord _root_.OAI.NuclearUltrapower.CuntzWords.instFintypeWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.VariableUltra.instCStarAlgebraAlgebra _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped ComplexOrder InnerProductSpace
namespace NuclearUltrapower.SOS.ElementarySpectral

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem delta_energy_oai (ρ : E →* (H ≃ₗᵢ[ℂ] H)) (x : H) :
    (inner ℂ x (eval (value (A := H →L[ℂ] H) (unitaryRep ρ)) delta x)).re = SOSEnergy.energy eGenSet ρ x / 2 := by
  rw [delta_eq_half_laplacian]
  simp only [smul_apply, inner_smul_right_eq_smul, laplacian_inner, Complex.real_smul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    unitaryRep_coe, LinearIsometryEquiv.coe_coe'']
  change (1/2 : ℝ) * SOSEnergy.energy eGenSet ρ x = _
  ring
end Hilbert
end NuclearUltrapower.SOS.ElementarySpectral
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.NuclearUltrapower.SOS.ElementarySpectral.delta_energy_oai.{u_1} := @OAI.NuclearUltrapower.SOS.ElementarySpectral.delta_energy_oai.{u_1}
