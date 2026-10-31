-- Prove2me | solution 1 for OAI.NuclearUltrapower.CuntzAveraging.defect_generator_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T13:02:15.249531+00:00
-- url     : https://prove2.me/submissions/ca1de226-71aa-4cdf-9432-2a32339a57a2

import Mathlib
import Definitions.Def_NuclearUltrapower
import Definitions.Def_OAIQ019N048
import Theorems.Thm_OAI_NuclearUltrapower_CuntzAveraging_rowSum_generator

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_CuntzAlgebra
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzWords.instFintypeWord _root_.OAI.NuclearUltrapower.VariableUltra.instCStarAlgebraAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAddCommGroupAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAlgebraComplexAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedRingAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instStarAlgebra _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped MonoidAlgebra

namespace NuclearUltrapower.CuntzUniversal
open UniformSpace CuntzPolynomial

/-- Seminorm-zero relations become literal equalities in the separated completion. -/
theorem inclusion_eq_of_models (x y : Poly)
    (h : ∀ (D : Type) [CStarAlgebra D] (r : Fin 2 → D), CuntzTwoRelations r →
      evaluate r x = evaluate r y) : inclusion x = inclusion y := by
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  rw [← map_sub]
  change ‖((x-y : Poly) : Completion Poly)‖ = 0
  rw [Completion.norm_coe]
  apply le_antisymm _ (norm_nonneg _)
  apply universalNorm_le
  intro D _ r hr
  rw [map_sub,h D r hr,sub_self,norm_zero]

theorem relations : CuntzTwoRelations generator := by
  constructor
  · intro i
    change star (inclusion (CuntzPolynomial.generator i)) * inclusion _ = 1
    rw [← map_star, ← map_mul, ← map_one inclusion]
    apply inclusion_eq_of_models
    intro D _ r hr
    simpa only [map_mul,map_star,map_one,evaluate_generator] using hr.1 i
  · change ∑ i, inclusion (CuntzPolynomial.generator i) * star (inclusion _) = 1
    simp only [← map_star, ← map_mul, ← map_sum]
    rw [← map_one inclusion]
    apply inclusion_eq_of_models
    intro D _ r hr
    simpa only [map_sum,map_mul,map_star,map_one,evaluate_generator] using hr.2

end NuclearUltrapower.CuntzUniversal
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_CuntzWords
attribute [-instance] _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.VariableUltra.instCStarAlgebraAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAddCommGroupAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAlgebraComplexAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedRingAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instStarAlgebra _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped InnerProductSpace
namespace NuclearUltrapower.CuntzWords

theorem index_injective (n : ℕ) : Function.Injective (@index n) := by
  induction n with
  | zero => exact fun _ _ _ => Subsingleton.elim _ _
  | succ n ih =>
    rintro ⟨i,w⟩ ⟨j,v⟩ h
    have hij : i = j := by
      by_contra hn
      exact CuntzModel.shiftIndex_disjoint hn (index w) (index v) h
    subst j
    have hw := ih ((CuntzModel.shiftIndex i).injective h)
    subst v
    rfl

/-- Completeness of the finite-length row is proved, not assumed. -/
theorem sum_range {D : Type*} [CStarAlgebra D] (r : Fin 2 → D) (hr : CuntzTwoRelations r)
    (n : ℕ) : ∑ w : Word n, value r w * star (value r w) = 1 := by
  induction n with
  | zero => simp [Word,value]
  | succ n ih =>
    change (∑ w : Fin 2 × Word n, value r (n := n+1) w * star (value r (n := n+1) w)) = (1 : D)
    rw [Fintype.sum_prod_type]
    simp only [value_succ,star_mul]
    have he (i : Fin 2) :
        (∑ w : Word n, (r i * value r w) * (star (value r w) * star (r i))) =
          r i * star (r i) := by
      calc
        _ = r i * (∑ w : Word n, value r w * star (value r w)) * star (r i) := by
          simp only [Finset.mul_sum,Finset.sum_mul,mul_assoc]
        _ = _ := by rw [ih,mul_one]
    simp only [he]
    exact hr.2

end NuclearUltrapower.CuntzWords
end
end

section

noncomputable section
open scoped TensorProduct InnerProductSpace
namespace NuclearUltrapower.CuntzAveraging
open CuntzModel CuntzWords CuntzUniversal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (R : Algebra →⋆ₙₐ[ℂ] (H →L[ℂ] H))

@[simp] theorem inner_row (n : ℕ) (x y : H) :
    ⟪row R n x, row R n y⟫_ℂ = ⟪x,R 1 y⟫_ℂ := by
  rw [row_apply,row_apply]
  simp only [sum_inner,inner_sum,inner_coordinate,(index_injective n).eq_iff,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  simp only [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_left]
  rw [← inner_sum]
  congr 1
  have h := congrArg (fun T : H →L[ℂ] H => T y)
    (congrArg R (sum_range generator CuntzUniversal.relations n))
  simpa only [map_sum,map_mul,map_star,sum_apply,mul_apply_eq_comp,
    ContinuousLinearMap.star_eq_adjoint] using h

theorem support_inner (x y : H) : ⟪R 1 x,R 1 y⟫_ℂ = ⟪x,R 1 y⟫_ℂ := by
  have hs : (R 1).adjoint * R 1 = R 1 := by
    rw [← ContinuousLinearMap.star_eq_adjoint,← map_star,star_one,← map_mul,one_mul]
  calc
    _ = ⟪x, (R 1).adjoint (R 1 y)⟫_ℂ :=
      (ContinuousLinearMap.adjoint_inner_right (R 1) x (R 1 y)).symm
    _ = _ := congrArg (fun T : H →L[ℂ] H => ⟪x,T y⟫_ℂ) hs

@[simp] theorem row_norm (n : ℕ) (x : H) : ‖row R n x‖ = ‖R 1 x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_eq_re_inner (𝕜 := ℂ),norm_sq_eq_re_inner (𝕜 := ℂ),inner_row,support_inner]

theorem support_norm_le (x : H) : ‖R 1 x‖ ≤ ‖x‖ := by
  have hR : ‖R 1‖ ≤ 1 := by simpa only [norm_one] using NonUnitalStarAlgHom.norm_apply_le R (1 : Algebra)
  simpa only [one_mul] using (R 1).le_of_opNorm_le hR x

theorem row_norm_le (n : ℕ) : ‖row R n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul,row_norm]
  exact support_norm_le R x

end NuclearUltrapower.CuntzAveraging
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_CuntzIntertwining
attribute [-instance] _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.VariableUltra.instCStarAlgebraAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAddCommGroupAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAlgebraComplexAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedRingAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instStarAlgebra _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner _root_.OAI.NuclearUltrapower.tensorBoundedSMul _root_.OAI.NuclearUltrapower.tensorHilbertNontrivial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Filter
open scoped TensorProduct InnerProductSpace Topology
namespace NuclearUltrapower.CuntzAveraging
open CuntzModel CuntzWords CuntzUniversal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (R : Algebra →⋆ₙₐ[ℂ] (H →L[ℂ] H))

theorem generator_norm_le (i : Fin 2) : ‖generator i‖ ≤ 1 := by
  simpa [CuntzPolynomial.evalLetter] using
    CuntzPolynomial.evalLetter_norm_le generator CuntzUniversal.relations (i,false)

attribute [local instance] OAI.NuclearUltrapower.CuntzAveraging.instIsBoundedSMulComplexTensorProductSubtypePreLpIndexMemAddSubgroupSpace
attribute [local instance] OAI.NuclearUltrapower.CuntzAveraging.instNormedSpaceComplexTarget
theorem rowSum_generator_bound (N : ℕ) (i : Fin 2) :
    ‖(rowSum R N).comp (R (generator i)) - (left i).comp (rowSum R N)‖ ≤ 2 := by
  rw [rowSum_generator]
  have hrow : ‖row R 0 - row R N‖ ≤ 2 :=
    (norm_sub_le (row R 0) (row R N)).trans (by linarith [row_norm_le R 0,row_norm_le R N])
  have hRi : ‖R (generator i)‖ ≤ 1 :=
    (NonUnitalStarAlgHom.norm_apply_le R _).trans (generator_norm_le i)
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (by nlinarith [norm_nonneg (row R 0-row R N),norm_nonneg (R (generator i))])

theorem defect_generator_bound_oai (n : ℕ) (i : Fin 2) :
    ‖defect R n (generator i)‖ ≤ ((n : ℝ)+1)⁻¹ * 2 := by
  have he : defect R n (generator i) = weight n •
      ((rowSum R ((n+1)^2)).comp (R (generator i)) - (left i).comp (rowSum R ((n+1)^2))) := by
    ext x
    change weight n • (rowSum R ((n+1)^2) (R (generator i) x)) -
      amplified (generator i) (weight n • rowSum R ((n+1)^2) x) =
      weight n • (rowSum R ((n+1)^2) (R (generator i) x) - left (H := H) i (rowSum R ((n+1)^2) x))
    rw [amplified_generator,map_smul,smul_sub]
  rw [he,norm_smul,weight_norm]
  exact mul_le_mul_of_nonneg_left (rowSum_generator_bound R _ i) (by positivity)

end NuclearUltrapower.CuntzAveraging
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.NuclearUltrapower.CuntzAveraging.defect_generator_bound_oai.{u_1} := @OAI.NuclearUltrapower.CuntzAveraging.defect_generator_bound_oai.{u_1}
