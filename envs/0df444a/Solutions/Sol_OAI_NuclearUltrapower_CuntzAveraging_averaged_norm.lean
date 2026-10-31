-- Prove2me | solution 1 for OAI.NuclearUltrapower.CuntzAveraging.averaged_norm
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T12:02:43.421911+00:00
-- url     : https://prove2.me/submissions/880585fb-d9f6-4b6c-848f-13c6818de683

import Mathlib
import Definitions.Def_NuclearUltrapower
import Definitions.Def_OAIQ019N039
import Definitions.Def_OAIQ019N040

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

theorem index_ne_of_length_ne {n m : ℕ} (hnm : n ≠ m) (w : Word n) (v : Word m) :
    index w ≠ index v := by
  intro h
  have hh := congrArg Prod.fst h
  simp only [index_height] at hh
  exact hnm (Int.ofNat_inj.mp hh)

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

@[simp] theorem inner_row_ne {n m : ℕ} (hnm : n ≠ m) (x y : H) :
    ⟪row R n x,row R m y⟫_ℂ = 0 := by
  simp only [row_apply,sum_inner,inner_sum,inner_coordinate,
    ite_eq_right (index_ne_of_length_ne hnm _ _),Finset.sum_const_zero]

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

end NuclearUltrapower.CuntzAveraging
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_CuntzIntertwining
attribute [-instance] _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.VariableUltra.instCStarAlgebraAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAddCommGroupAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAlgebraComplexAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedRingAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instStarAlgebra _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
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

theorem inner_rows (n m : ℕ) (x y : H) :
    ⟪row R n x,row R m y⟫_ℂ = if n = m then ⟪x,R 1 y⟫_ℂ else 0 := by
  split_ifs with h
  · subst m; exact inner_row R n x y
  · exact inner_row_ne R h x y

theorem inner_rowSum (N : ℕ) (x y : H) :
    ⟪rowSum R N x, rowSum R N y⟫_ℂ = (N : ℂ) * ⟪x,R 1 y⟫_ℂ := by
  simp only [rowSum_apply,sum_inner,inner_sum,inner_rows,Finset.sum_ite_eq',
    Finset.sum_ite_mem,Finset.sum_const,Finset.inter_self,Finset.card_range,nsmul_eq_mul]

theorem rowSum_norm_sq (N : ℕ) (x : H) :
    ‖rowSum R N x‖^2 = (N : ℝ) * ‖R 1 x‖^2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ),inner_rowSum,← support_inner]
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  simp

@[simp] theorem averaged_norm_oai (n : ℕ) (x : H) : ‖averaged R n x‖ = ‖R 1 x‖ := by
  have hn : (n : ℝ)+1 ≠ 0 := by positivity
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  change ‖weight n • rowSum R ((n+1)^2) x‖^2 = _
  simp only [norm_smul,weight_norm,mul_pow,rowSum_norm_sq,
    Nat.cast_pow,Nat.cast_add,Nat.cast_one]
  field_simp

end NuclearUltrapower.CuntzAveraging
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.NuclearUltrapower.CuntzAveraging.averaged_norm_oai.{u_1} := @OAI.NuclearUltrapower.CuntzAveraging.averaged_norm_oai.{u_1}
