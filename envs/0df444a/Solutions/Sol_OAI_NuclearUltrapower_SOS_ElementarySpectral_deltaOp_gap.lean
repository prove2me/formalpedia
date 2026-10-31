-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.ElementarySpectral.deltaOp_gap
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T17:15:15.694239+00:00
-- url     : https://prove2.me/submissions/10d12858-069c-4c72-a061-ab4e570990f9

import Mathlib
import Definitions.Def_OAIQ019N044
import Theorems.Thm_OAI_NuclearUltrapower_SOS_ElementarySpectral_deltaOp_nonneg
import Theorems.Thm_OAI_NuclearUltrapower_SOS_ElementarySpectral_deltaOp_sq_gap
import Theorems.Thm_OAI_NuclearUltrapower_SOS_ElementarySpectral_delta_energy

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_SOSGap
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarPoly _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarWord _root_.OAI.NuclearUltrapower.CuntzPolynomial.instSeminormedRingPoly _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarPoly _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.VariableUltra.instCStarAlgebraAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNontrivialAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedRingAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instStarAlgebra _root_.OAI.NuclearUltrapower.instStarNormUltrapower _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner _root_.OAI.NuclearUltrapower.tensorHilbertNontrivial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped InnerProductSpace

noncomputable section
open scoped InnerProductSpace ComplexOrder
namespace NuclearUltrapower
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A sums-of-squares inequality for a positive operator produces a true gap
on the orthogonal complement of its kernel; no finite-dimensional hypothesis. -/
theorem positive_sq_gap (T : H →L[ℂ] H) (hT : 0 ≤ T) (κ : ℝ)
    (hgap : κ • T ≤ T*T) (x : H) (hx : x ∈ T.kerᗮ) :
    κ * ‖x‖ ^ 2 ≤ (inner ℂ x (T x)).re := by
  let R := CFC.sqrt T
  have hR : IsSelfAdjoint R := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg T)
  have hRR : R * R = T := CFC.sqrt_mul_sqrt_self T hT
  have hRnorm (y : H) : ‖R y‖ ^ 2 = (inner ℂ y (T y)).re := by
    rw [← hRR, mul_apply_eq_comp]
    have hr := hR.isSymmetric y (R y)
    change inner ℂ (R y) (R y) = inner ℂ y (R (R y)) at hr
    rw [← hr]
    exact norm_sq_eq_re_inner (𝕜 := ℂ) (R y)
  have hker : R.ker = T.ker := by
    ext y
    change R y = 0 ↔ T y = 0
    constructor
    · intro h; rw [← hRR, mul_apply_eq_comp, h, map_zero]
    · intro h
      apply norm_eq_zero.mp
      have hn := hRnorm y
      rw [h, inner_zero_right, Complex.zero_re] at hn
      nlinarith [norm_nonneg (R y)]
  have hd : R.range.topologicalClosure = T.kerᗮ := by
    rw [← hker, R.orthogonal_ker]
    congr 1
    exact congrArg (fun A : H →L[ℂ] H => A.toLinearMap.range) hR.star_eq.symm
  have hc : IsClosed {y : H | κ * ‖y‖ ^ 2 ≤ (inner ℂ y (T y)).re} :=
    isClosed_le (by fun_prop) (by fun_prop)
  have hs : (R.range : Set H) ⊆ {y : H | κ * ‖y‖ ^ 2 ≤ (inner ℂ y (T y)).re} := by
    rintro _ ⟨y, rfl⟩
    change κ * ‖R y‖ ^ 2 ≤ (inner ℂ (R y) (T (R y))).re
    have hp := ((ContinuousLinearMap.le_def _ _).mp hgap).re_inner_nonneg_right y
    have hTy : T (R y) = R (T y) := by
      rw [← hRR]
      simp only [mul_apply_eq_comp]
    have hr := hR.isSymmetric (R y) (T y)
    change inner ℂ (R (R y)) (T y) = inner ℂ (R y) (R (T y)) at hr
    rw [hRnorm, hTy, ← hr, ← mul_apply_eq_comp, hRR]
    apply sub_nonneg.mp
    change 0 ≤ (inner ℂ y ((T*T - κ • T) y)).re at hp
    have ht := (IsSelfAdjoint.of_nonneg hT).isSymmetric y (T y)
    change inner ℂ (T y) (T y) = inner ℂ y (T (T y)) at ht
    simpa only [sub_apply, mul_apply_eq_comp, smul_apply, inner_sub_right,
      inner_smul_right_eq_smul, Complex.sub_re, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, ← ht] using hp
  apply (closure_minimal hs hc)
  change x ∈ (R.range.topologicalClosure : Set H)
  rwa [hd]
end NuclearUltrapower

end
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_IntegralCertificate
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzWords.instDecidableEqWord _root_.OAI.NuclearUltrapower.CuntzWords.instFintypeWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
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

theorem deltaOp_gap_oai (ρ : E →* (H ≃ₗᵢ[ℂ] H)) (x : H) (hx : x ∈ (deltaOp ρ).kerᗮ) :
    (1/10 : ℝ) * ‖x‖ ^ 2 ≤ SOSEnergy.energy eGenSet ρ x := by
  have h := positive_sq_gap (deltaOp ρ) (deltaOp_nonneg ρ) (1/20) (deltaOp_sq_gap ρ) x hx
  rw [deltaOp_energy] at h
  linarith

end Hilbert
end NuclearUltrapower.SOS.ElementarySpectral
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.NuclearUltrapower.SOS.ElementarySpectral.deltaOp_gap_oai.{u_1} := @OAI.NuclearUltrapower.SOS.ElementarySpectral.deltaOp_gap_oai.{u_1}
