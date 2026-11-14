-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.ElementarySpectral.deltaOp_energy_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T10:35:19.927748+00:00
-- url     : https://prove2.me/submissions/8fa9b28a-094e-4116-bc54-980fe1fe2fad

import Mathlib
import Definitions.Def_OAIQ229C037
import Theorems.Thm_OAI_NuclearUltrapower_SOS_ElementarySpectral_sum_gen_star_ca

section
-- module Solutions.Q229_CA.NuclearUltrapower_SOSSemantics
attribute [-instance] _root_.OAI.CoarseAssembly.baseUnionDecidableEq _root_.OAI.CoarseAssembly.instFintypeFiberVertex _root_.OAI.CoarseAssembly.vertexUnionDecidableEq _root_.OAI.NuclearUltrapower.strongDualInner
attribute [-simp] _root_.OAI.CoarseAssembly.adjoint_apply_isometry _root_.OAI.NuclearUltrapower.Elementary.integralTheta_left _root_.OAI.NuclearUltrapower.Elementary.integralTheta_pow_translation _root_.OAI.NuclearUltrapower.Elementary.integralTheta_right _root_.OAI.NuclearUltrapower.Elementary.integralTheta_translation _root_.OAI.NuclearUltrapower.Elementary.residuePermutation_apply _root_.OAI.NuclearUltrapower.Elementary.residueUnitary_apply _root_.OAI.NuclearUltrapower.Elementary.residue_one _root_.OAI.NuclearUltrapower.Elementary.residue_theta _root_.OAI.NuclearUltrapower.SOS.ElementarySpectral.unitaryRep_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SOS

theorem toMatrix_one : toMatrix matOne = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem interpret_coe (m : Mat3) (h : (toMatrix m).det = 1) :
    (interpret m : Matrix (Fin 3) (Fin 3) ℤ) = toMatrix m := by
  simp [interpret, h]

theorem interpret_one : interpret matOne = 1 := by
  apply Subtype.ext
  rw [interpret_coe _ (by rw [toMatrix_one, Matrix.det_one]), toMatrix_one]
  rfl

end NuclearUltrapower.SOS

end

end OAI
end

section
-- module Solutions.Q229_CA.NuclearUltrapower_IntegerMatrices
attribute [-instance] _root_.OAI.CoarseAssembly.baseUnionDecidableEq _root_.OAI.CoarseAssembly.instFintypeFiberVertex _root_.OAI.CoarseAssembly.vertexUnionDecidableEq _root_.OAI.NuclearUltrapower.strongDualInner
attribute [-simp] _root_.OAI.CoarseAssembly.adjoint_apply_isometry _root_.OAI.NuclearUltrapower.Elementary.integralTheta_left _root_.OAI.NuclearUltrapower.Elementary.integralTheta_pow_translation _root_.OAI.NuclearUltrapower.Elementary.integralTheta_right _root_.OAI.NuclearUltrapower.Elementary.integralTheta_translation _root_.OAI.NuclearUltrapower.Elementary.residuePermutation_apply _root_.OAI.NuclearUltrapower.Elementary.residueUnitary_apply _root_.OAI.NuclearUltrapower.Elementary.residue_one _root_.OAI.NuclearUltrapower.Elementary.residue_theta _root_.OAI.NuclearUltrapower.SOS.ElementarySpectral.unitaryRep_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace NuclearUltrapower.SOS

theorem generators_det : ∀ m ∈ generators, (toMatrix m).det = 1 := by
  decide +kernel

theorem goodWord_one : GoodWord 0 matOne := by
  refine ⟨by rw [toMatrix_one, Matrix.det_one], [], ?_, by simp, by simp⟩
  simp only [List.prod_nil, interpret_one]

theorem goodWord_generator {m : Mat3} (hm : m ∈ generators) : GoodWord 1 m := by
  refine ⟨generators_det m hm, [interpret m], by simp, by simp, ?_⟩
  intro s hs
  have : s = interpret m := by simpa using hs
  subst s
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨m, hm, rfl⟩)

end NuclearUltrapower.SOS
end
end

section

noncomputable section
namespace NuclearUltrapower.SOS

theorem goodWord_mem {n : ℕ} {m : Mat3} (h : GoodWord n m) : interpret m ∈ elementary := by
  obtain ⟨_, w, hw, _, hs⟩ := h
  rw [← hw]
  exact elementary.list_prod_mem (fun g hg => Subgroup.subset_closure (hs g hg))

theorem eInterpret_coe {n : ℕ} {m : Mat3} (h : GoodWord n m) :
    (eInterpret m : SL) = interpret m := by
  simp only [eInterpret, dite_eq_left (goodWord_mem h)]

@[simp] theorem eInterpret_one : eInterpret matOne = 1 := by
  apply Subtype.ext
  rw [eInterpret_coe goodWord_one, interpret_one]
  rfl

end NuclearUltrapower.SOS
end
end

end OAI
end

section
-- module Solutions.Q229_CA.NuclearUltrapower_Laplacian
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
attribute [-simp] _root_.OAI.CoarseAssembly.adjoint_apply_isometry
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
-- module Solutions.Q229_CA.NuclearUltrapower_SOSGap
attribute [-instance] _root_.OAI.CoarseAssembly.baseUnionDecidableEq _root_.OAI.CoarseAssembly.instFintypeFiberVertex _root_.OAI.CoarseAssembly.vertexUnionDecidableEq _root_.OAI.NuclearUltrapower.strongDualInner
attribute [-simp] _root_.OAI.CoarseAssembly.adjoint_apply_isometry _root_.OAI.NuclearUltrapower.Elementary.integralTheta_left _root_.OAI.NuclearUltrapower.Elementary.integralTheta_pow_translation _root_.OAI.NuclearUltrapower.Elementary.integralTheta_right _root_.OAI.NuclearUltrapower.Elementary.integralTheta_translation _root_.OAI.NuclearUltrapower.Elementary.residuePermutation_apply _root_.OAI.NuclearUltrapower.Elementary.residueUnitary_apply _root_.OAI.NuclearUltrapower.Elementary.residue_one _root_.OAI.NuclearUltrapower.Elementary.residue_theta
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped ComplexOrder InnerProductSpace
namespace NuclearUltrapower.SOS.ElementarySpectral

theorem genList_nodup : (generators.map eInterpret).Nodup := by
  have h : (generators.map interpret).Nodup := by decide +kernel
  have he : (generators.map eInterpret).map (fun g : E => (g : SL)) = generators.map interpret := by
    rw [List.map_map]
    apply List.map_congr_left
    intro m hm
    exact eInterpret_coe (goodWord_generator hm)
  rw [← he] at h
  exact List.Nodup.of_map _ h

theorem eGenSet_card : eGenSet.card = 12 := by
  rw [eGenSet, List.toFinset_card_of_nodup genList_nodup]
  rfl

section Algebra
variable {A : Type*} [CStarAlgebra A]

@[simp] theorem value_one (ρ : E →* unitary A) : value ρ matOne = 1 := by
  simp [value, eInterpret_one]

theorem delta_value (ρ : E →* unitary A) :
    eval (value ρ) delta = (12 : ℤ) • (1:A) - ∑ g ∈ eGenSet, (ρ g : A) := by
  rw [eGenSet, List.sum_toFinset _ genList_nodup]
  simp only [delta, eval, List.map_cons, List.map_map, Function.comp_def,
    List.sum_cons, neg_one_zsmul]
  rw [value_one]
  simp only [List.sum_neg, sub_eq_add_neg, value, List.map_map, Function.comp_def]

theorem laplacian_eq_delta (ρ : E →* unitary A) :
    laplacian eGenSet (fun g => (ρ g : A)) = (2 : ℝ) • eval (value ρ) delta := by
  have h (g : E) : star ((ρ g : A) - 1) * ((ρ g : A) - 1) =
      1 - star (ρ g : A) - (ρ g : A) + 1 := by
    simp only [star_sub, star_one, sub_mul, mul_sub, Unitary.coe_star_mul_self,
      one_mul, mul_one]
    abel
  simp only [laplacian, h, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    sum_gen_star_ca, Finset.sum_const, eGenSet_card, delta_value]
  module

theorem delta_eq_half_laplacian (ρ : E →* unitary A) :
    eval (value ρ) delta = (1/2 : ℝ) • laplacian eGenSet (fun g => (ρ g : A)) := by
  rw [laplacian_eq_delta, smul_smul]
  norm_num

end Algebra

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem delta_energy (ρ : E →* (H ≃ₗᵢ[ℂ] H)) (x : H) :
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

section
-- module Solutions.Q229_CA.NuclearUltrapower_IntegralCertificate
attribute [-instance] _root_.OAI.CoarseAssembly.baseUnionDecidableEq _root_.OAI.CoarseAssembly.instFintypeFiberVertex _root_.OAI.CoarseAssembly.vertexUnionDecidableEq _root_.OAI.NuclearUltrapower.strongDualInner
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

theorem deltaOp_energy_ca_oai (ρ : E →* (H ≃ₗᵢ[ℂ] H)) (x : H) :
    (inner ℂ x (deltaOp ρ x)).re = SOSEnergy.energy eGenSet ρ x / 2 :=
  delta_energy ρ x

end Hilbert
end NuclearUltrapower.SOS.ElementarySpectral
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.NuclearUltrapower.SOS.ElementarySpectral.deltaOp_energy_ca_oai.{u_1} := @OAI.NuclearUltrapower.SOS.ElementarySpectral.deltaOp_energy_ca_oai.{u_1}
