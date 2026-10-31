-- Prove2me | solution 1 for OAI.NuclearUltrapower.CuntzAveraging.commutingEval_norm_le_min
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T13:00:33.880143+00:00
-- url     : https://prove2.me/submissions/f6b0d1f8-b90d-4987-8c37-ff8c7cce7c8f

import Mathlib
import Definitions.Def_NuclearUltrapower
import Definitions.Def_OAIQ019N041
import Definitions.Def_OAIQ019N048
import Theorems.Thm_OAI_NuclearUltrapower_CuntzAveraging_averaged_norm
import Theorems.Thm_OAI_NuclearUltrapower_CuntzAveraging_averaged_norm_le
import Theorems.Thm_OAI_NuclearUltrapower_CuntzAveraging_jointDefect_tendsto

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_HilbertTensor
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instSeminormedRingPoly _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarPoly _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAddCommGroupAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instStarAlgebra _root_.OAI.NuclearUltrapower.instStarNormUltrapower _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner _root_.OAI.NuclearUltrapower.tensorHilbertNontrivial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
noncomputable section
open scoped TensorProduct InnerProductSpace
open Module.End
noncomputable section
open scoped CStarAlgebra
noncomputable section
open Filter
open scoped Topology ENNReal
noncomputable section
open scoped InnerProductSpace
noncomputable section
open scoped TensorProduct InnerProductSpace
namespace NuclearUltrapower

section TensorOperators
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

variable [CompleteSpace E] [CompleteSpace F]

theorem tensorLeftRight_mul (U : E →L[ℂ] E) (V : F →L[ℂ] F) :
    tensorLeftHom U * tensorRightHom V = completedTensorMap U V := by
  change completedTensorMap U 1 * completedTensorMap 1 V = _
  rw [← completedTensorMap_mul, mul_one, one_mul]

end TensorOperators
end NuclearUltrapower

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_TensorNorms
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarPoly _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarWord _root_.OAI.NuclearUltrapower.CuntzPolynomial.instSeminormedRingPoly _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarPoly _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.VariableUltra.instCStarAlgebraAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instCompleteSpaceAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAddCommGroupAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instStarAlgebra _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner _root_.OAI.NuclearUltrapower.tensorBoundedSMul _root_.OAI.NuclearUltrapower.tensorHilbertNontrivial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
noncomputable section
open scoped TensorProduct InnerProductSpace
open Module.End
noncomputable section
open scoped CStarAlgebra
noncomputable section
open Filter
open scoped Topology ENNReal
noncomputable section
open scoped InnerProductSpace
noncomputable section
open scoped TensorProduct InnerProductSpace
noncomputable section
open scoped TensorProduct
namespace NuclearUltrapower

section NormTransfer

variable {B : Type u} {C : Type v} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]

local instance spatialTensorBoundedSMul_r687e26_1 (H K : ComplexHilbert.{w}) :
    IsBoundedSMul ℂ (H ⊗[ℂ] K) := NormedSpace.toIsBoundedSMul
/-- Uniform finite projective bound on all spatial and commuting evaluations.
In particular the real suprema defining the tensor norms are genuine bounds. -/
theorem evals_bounded (x : B ⊗[ℂ] C) :
    ∃ M : ℝ, (∀ (H K : ComplexHilbert.{w})
      (ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (σ : C →⋆ₙₐ[ℂ] (K →L[ℂ] K)),
      ‖spatialEval H K ρ σ x‖ ≤ M) ∧
      (∀ (H : ComplexHilbert.{w}) (ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H))
      (σ : C →⋆ₙₐ[ℂ] (H →L[ℂ] H)), ‖commutingEval H ρ σ x‖ ≤ M) := by
  induction x using OAI.tensorInductionOn with
  | tmul b c =>
    refine ⟨‖b‖ * ‖c‖, ?_, ?_⟩
    · intro H K ρ σ
      exact (TensorProduct.norm_mapL_le _ _).trans
        (mul_le_mul (NonUnitalStarAlgHom.norm_apply_le ρ b)
          (NonUnitalStarAlgHom.norm_apply_le σ c) (norm_nonneg _) (norm_nonneg _))
    · intro H ρ σ
      exact (norm_mul_le _ _).trans
        (mul_le_mul (NonUnitalStarAlgHom.norm_apply_le ρ b)
          (NonUnitalStarAlgHom.norm_apply_le σ c) (norm_nonneg _) (norm_nonneg _))
  | add x y hx hy =>
    obtain ⟨M, hM, hM'⟩ := hx
    obtain ⟨N, hN, hN'⟩ := hy
    refine ⟨M + N, ?_, ?_⟩
    · intro H K ρ σ
      rw [map_add]
      exact (norm_add_le (spatialEval H K ρ σ x) (spatialEval H K ρ σ y)).trans
        (add_le_add (hM H K ρ σ) (hN H K ρ σ))
    · intro H ρ σ
      rw [map_add]
      exact (norm_add_le _ _).trans (add_le_add (hM' H ρ σ) (hN' H ρ σ))

theorem norm_spatialEval_le (x : B ⊗[ℂ] C) (H K : ComplexHilbert.{w})
    (ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (σ : C →⋆ₙₐ[ℂ] (K →L[ℂ] K)) :
    ‖spatialEval H K ρ σ x‖ ≤ minTensorNorm.{u,v,w} x := by
  obtain ⟨M, hM, _⟩ := evals_bounded.{u,v,w} x
  unfold minTensorNorm
  apply le_csSup
  · refine ⟨M, ?_⟩
    rintro _ ⟨H, K, ρ, σ, rfl⟩
    exact hM H K ρ σ
  · exact ⟨H, K, ρ, σ, rfl⟩

end NormTransfer
end NuclearUltrapower

end
end
end
end
end
end
end

section

noncomputable section
open scoped TensorProduct
namespace NuclearUltrapower

section Bounds
variable {A C : Type} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra C]

attribute [local instance] OAI.NuclearUltrapower.instIsBoundedSMulComplexTensorProductCarrier
theorem minTensorNorm_nonneg (x : A ⊗[ℂ] C) : 0 ≤ minTensorNorm.{0,0,0} x :=
  (norm_nonneg (spatialEval scalarHilbert scalarHilbert
    (0 : A →⋆ₙₐ[ℂ] (ℂ →L[ℂ] ℂ)) (0 : C →⋆ₙₐ[ℂ] (ℂ →L[ℂ] ℂ)) x)).trans
    (norm_spatialEval_le x scalarHilbert scalarHilbert 0 0)

/-- Spatial evaluation is the commuting evaluation on the Hilbert completion;
completion does not change its operator norm. -/
theorem completed_spatial_eq (H K : ComplexHilbert.{0})
    (R : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (S : C →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (x : A ⊗[ℂ] C) :
    (spatialEval H K R S x).completion =
      commutingEval ⟨TensorHilbert H K⟩ (tensorLeftRep R) (tensorRightRep S) x := by
  induction x using OAI.tensorInductionOn with
  | tmul a c =>
    rw [spatialEval_tmul,commutingEval_tmul,tensorLeftRep_apply,tensorRightRep_apply,
      tensorLeftRight_mul]
    rfl
  | add x y hx hy => simp only [map_add,completed_add,hx,hy]

end Bounds
end NuclearUltrapower
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_CuntzNuclearity
attribute [-instance] _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.VariableUltra.instCStarAlgebraAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instCompleteSpaceAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAddCommGroupAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAlgebraComplexAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedRingAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instStarAlgebra _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner _root_.OAI.NuclearUltrapower.tensorBoundedSMul _root_.OAI.NuclearUltrapower.tensorHilbertNontrivial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Filter
open scoped TensorProduct Topology
namespace NuclearUltrapower
namespace CuntzAveraging
open CuntzUniversal CuntzModel

variable {C : Type} [NonUnitalCStarAlgebra C] (H : ComplexHilbert.{0})
  (R : Algebra →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (S : C →⋆ₙₐ[ℂ] (H →L[ℂ] H))

attribute [local instance] OAI.NuclearUltrapower.CuntzAveraging.instIsBoundedSMulComplexTensorProductSubtypePreLpIndexMemAddSubgroupSpaceCarrier
attribute [local instance] OAI.NuclearUltrapower.CuntzAveraging.instNormedSpaceComplexTargetCarrier
theorem completedEval_norm_le (x : Algebra ⊗[ℂ] C) :
    ‖completedEval H S x‖ ≤ minTensorNorm.{0,0,0} x := by
  change ‖commutingEval ⟨Target H⟩
    (tensorLeftRep (H := ⟨Space⟩) (K := H) concrete.toNonUnitalStarAlgHom)
    (tensorRightRep (H := ⟨Space⟩) (K := H) S) x‖ ≤ _
  calc
    _ = ‖(spatialEval ⟨Space⟩ H concrete.toNonUnitalStarAlgHom S x).completion‖ :=
      congrArg norm (completed_spatial_eq ⟨Space⟩ H concrete.toNonUnitalStarAlgHom S x).symm
    _ = ‖spatialEval ⟨Space⟩ H concrete.toNonUnitalStarAlgHom S x‖ := completed_norm _
    _ ≤ _ := norm_spatialEval_le x ⟨Space⟩ H concrete.toNonUnitalStarAlgHom S

/-- The output of any commuting tensor evaluation lies in the support of R. -/
theorem commutingEval_support (x : Algebra ⊗[ℂ] C) :
    R 1 * commutingEval H R S x = commutingEval H R S x := by
  induction x using OAI.tensorInductionOn with
  | tmul a c =>
    change R 1 * (R a * S c) = R a * S c
    rw [← mul_assoc,← map_mul,one_mul]
  | add x y hx hy =>
    erw [map_add (commutingEval H R S)]
    rw [mul_add,hx,hy]

/-- Averaging proves the nontrivial maximal-to-minimal inequality directly;
no faithfulness, separability or nondegeneracy of the input representations is
assumed. -/
theorem commutingEval_norm_le_min_oai (hRS : ∀ a c, Commute (R a) (S c)) (x : Algebra ⊗[ℂ] C) :
    ‖commutingEval H R S x‖ ≤ minTensorNorm.{0,0,0} x := by
  apply ContinuousLinearMap.opNorm_le_bound _ (minTensorNorm_nonneg x)
  intro v
  have hs : R 1 (commutingEval H R S x v) = commutingEval H R S x v :=
    congrArg (fun T : H →L[ℂ] H => T v) (commutingEval_support H R S x)
  have hb (n : ℕ) : ‖commutingEval H R S x v‖ ≤
      ‖jointDefect H R S n x‖ * ‖v‖ + minTensorNorm.{0,0,0} x * ‖v‖ := by
    calc
      _ = ‖averaged R n (commutingEval H R S x v)‖ := by rw [averaged_norm,hs]
      _ = ‖jointDefect H R S n x v + completedEval H S x (averaged R n v)‖ := by
        rw [jointDefect,sub_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,sub_add_cancel]
      _ ≤ ‖jointDefect H R S n x v‖ + ‖completedEval H S x (averaged R n v)‖ := norm_add_le _ _
      _ ≤ ‖jointDefect H R S n x‖ * ‖v‖ + minTensorNorm.{0,0,0} x * ‖v‖ := by
        apply add_le_add (ContinuousLinearMap.le_opNorm _ _)
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul (completedEval_norm_le H S x)
            ((averaged R n).le_of_opNorm_le (averaged_norm_le R n) v |>.trans_eq (one_mul _))
            (norm_nonneg _) (minTensorNorm_nonneg x))
  have ht := ((jointDefect_tendsto H R S hRS x).norm.mul_const ‖v‖).add_const
    (minTensorNorm.{0,0,0} x * ‖v‖)
  simpa only [norm_zero,zero_mul,zero_add] using
    ge_of_tendsto ht (Filter.Eventually.of_forall hb)

end CuntzAveraging

end NuclearUltrapower
end
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.CuntzAveraging.commutingEval_norm_le_min_oai := @OAI.NuclearUltrapower.CuntzAveraging.commutingEval_norm_le_min_oai
