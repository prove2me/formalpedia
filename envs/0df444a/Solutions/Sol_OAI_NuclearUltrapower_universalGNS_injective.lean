-- Prove2me | solution 1 for OAI.NuclearUltrapower.universalGNS_injective
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T12:56:39.574994+00:00
-- url     : https://prove2.me/submissions/7e1c0845-b53f-46fc-93e3-c3c050418bdf

import Mathlib
import Definitions.Def_OAIQ019N041
import Theorems.Thm_OAI_NuclearUltrapower_exists_norming_state

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_FaithfulGNS
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarWord _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.VariableUltra.instCStarAlgebraAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instCompleteSpaceAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAddCommGroupAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAlgebraComplexAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedRingAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instStarAlgebra _root_.OAI.NuclearUltrapower.instStarNormUltrapower _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
universe u
open scoped ComplexOrder ENNReal
namespace NuclearUltrapower
variable {A : Type u} [CStarAlgebra A] [Nontrivial A]

attribute [local instance] OAI.NuclearUltrapower.gnsSpectralOrder
attribute [local instance] OAI.NuclearUltrapower.gnsSpectralOrderedRing
omit [Nontrivial A] in
/-- The GNS cyclic vector for a state has norm one. -/
theorem gns_unit_norm (f : A →ₚ[ℂ] ℂ) (h1 : f 1 = 1) :
    ‖(f.toPreGNS 1 : f.GNS)‖ = 1 := by
  rw [UniformSpace.Completion.norm_coe, f.preGNS_norm_def]
  simp [h1]

/-- Every C*-algebra element attains its norm in one of its GNS representations.
This supplies norm-separation with no external faithful-representation axiom. -/
theorem exists_norming_gns (a : A) :
    ∃ f : A →ₚ[ℂ] ℂ, f 1 = 1 ∧ ‖f.gnsStarAlgHom a‖ = ‖a‖ := by
  obtain ⟨f, h1, hf⟩ := exists_norming_state (star a * a) (star_mul_self_nonneg a)
  refine ⟨f, h1, le_antisymm (NonUnitalStarAlgHom.norm_apply_le _ _) ?_⟩
  let ξ : f.GNS := f.toPreGNS 1
  have hξ : ‖ξ‖ = 1 := gns_unit_norm f h1
  have hact : f.gnsStarAlgHom a ξ = (f.toPreGNS a : f.GNS) := by
    change f.gnsNonUnitalStarAlgHom a (f.toPreGNS 1) = _
    rw [f.gnsNonUnitalStarAlgHom_apply_coe]
    simp [PositiveLinearMap.leftMulMapPreGNS]
  have hn : ‖f.gnsStarAlgHom a ξ‖ = ‖a‖ := by
    rw [hact, UniformSpace.Completion.norm_coe, f.preGNS_norm_def]
    simp only [PositiveLinearMap.ofPreGNS_toPreGNS, hf, Complex.ofReal_re,
      CStarRing.norm_star_mul_self]
    rw [Real.sqrt_mul_self (norm_nonneg _)]
  have h := (f.gnsStarAlgHom a).le_opNorm ξ
  rwa [hξ, mul_one, hn] at h

theorem universalGNS_injective_oai : Function.Injective (universalGNS (A := A)) := by
  classical
  apply (injective_iff_map_eq_zero _).mpr
  intro a ha
  obtain ⟨f, h1, hf⟩ := exists_norming_gns a
  have hz : f.gnsStarAlgHom a = 0 := by
    ext ξ
    have he := congrArg (fun T : UniversalGNS A →L[ℂ] UniversalGNS A =>
      T (lp.single 2 f ξ) f) ha
    simpa only [universalGNS_apply, lp.single_apply, Pi.single_eq_same, dite_true,
      zero_apply, lp.coeFn_zero, Pi.zero_apply] using he
  rw [hz, norm_zero] at hf
  exact norm_eq_zero.mp hf.symm

end NuclearUltrapower
end
end

end OAI
end

theorem solution.{u} : type_of% @OAI.NuclearUltrapower.universalGNS_injective_oai.{u} := @OAI.NuclearUltrapower.universalGNS_injective_oai.{u}
