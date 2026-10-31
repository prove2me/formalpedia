-- Prove2me | solution 1 for OAI.NuclearUltrapower.main_no_embedding
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T13:09:15.104993+00:00
-- url     : https://prove2.me/submissions/ccd1f30d-2dab-43ad-a162-f7d0051faca4

import Mathlib
import Definitions.Def_NuclearUltrapower
import Definitions.Def_OAIQ019N041
import Definitions.Def_OAIQ019N048
import Theorems.Thm_OAI_NuclearUltrapower_CuntzAveraging_commutingEval_norm_le_min
import Theorems.Thm_OAI_NuclearUltrapower_main_statement

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

/-- Values on the two generators determine all continuous model maps. -/
theorem modelMap_unique {D : Type} [CStarAlgebra D] (r : Fin 2 → D)
    (hr : CuntzTwoRelations r) (φ : Algebra →⋆ₐ[ℂ] D)
    (hφ : ∀ i, φ (generator i) = r i) : φ = modelMap r hr := by
  have hletter (a : Letter) : φ (inclusion (MonoidAlgebra.of ℂ Word (FreeMonoid.of a))) =
      evalLetter r a := by
    rcases a with ⟨i,b⟩
    cases b
    · exact hφ i
    · change φ (inclusion (MonoidAlgebra.single (FreeMonoid.of (i,true)) 1)) = star (r i)
      have hg : (MonoidAlgebra.single (FreeMonoid.of (i,true)) 1 : Poly) =
          star (CuntzPolynomial.generator i) := by
        rw [CuntzPolynomial.generator,star_single,star_word_of,star_one]
        rfl
      rw [hg,map_star,map_star]
      exact congrArg star (hφ i)
  have hw (w : Word) : φ (inclusion (MonoidAlgebra.of ℂ Word w)) = evalWord r w := by
    induction w using FreeMonoid.recOn with
    | one =>
      change φ (inclusion 1) = evalWord r 1
      simp only [map_one]
    | of_mul a w ih => simp only [map_mul,hletter,ih,evalWord_of]
  have he (x : Poly) : φ (inclusion x) = modelMap r hr (inclusion x) := by
    rw [modelMap_coe]
    induction x using MonoidAlgebra.induction_on with
    | of w => simpa only [MonoidAlgebra.of_apply,evaluate_single,one_smul] using hw w
    | add x y hx hy => simp only [map_add,hx,hy]
    | smul c x hx => simp only [map_smul,hx]
  have hc (f : Algebra →⋆ₐ[ℂ] D) : Continuous f :=
    AddMonoidHomClass.continuous_of_bound f 1 (fun x => by
      simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le f x)
  apply DFunLike.ext'
  exact Completion.denseRange_coe.equalizer (hc φ) (hc (modelMap r hr)) (funext he)

theorem universal : IsCuntzTwoAlgebra bundled generator := by
  refine ⟨relations, ?_⟩
  intro D r hr
  exact ⟨modelMap r hr, modelMap_generator r hr, fun φ hφ => modelMap_unique r hr φ hφ⟩

end NuclearUltrapower.CuntzUniversal
end
end

end OAI
end

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

theorem tensorLeftRight_commute (U : E →L[ℂ] E) (V : F →L[ℂ] F) :
    Commute (tensorLeftHom U) (tensorRightHom V) := by
  change completedTensorMap U 1 * completedTensorMap 1 V = completedTensorMap 1 V * completedTensorMap U 1
  simp only [← completedTensorMap_mul, mul_one, one_mul]
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

local instance spatialTensorBoundedSMul_r2c1f1d_1 (H K : ComplexHilbert.{w}) :
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

theorem norm_commutingEval_le (x : B ⊗[ℂ] C) (H : ComplexHilbert.{w})
    (ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (σ : C →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (hcomm : ∀ b c, Commute (ρ b) (σ c)) :
    ‖commutingEval H ρ σ x‖ ≤ maxTensorNorm.{u,v,w} x := by
  obtain ⟨M, _, hM⟩ := evals_bounded.{u,v,w} x
  unfold maxTensorNorm
  apply le_csSup
  · refine ⟨M, ?_⟩
    rintro _ ⟨H, ρ, σ, _, rfl⟩
    exact hM H ρ σ
  · exact ⟨H, ρ, σ, hcomm, rfl⟩

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
theorem tensor_reps_commute (H K : ComplexHilbert.{0})
    (R : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (S : C →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (a : A) (c : C) :
    Commute (tensorLeftRep (K := K) R a) (tensorRightRep (H := H) S c) :=
  tensorLeftRight_commute _ _

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

/-- The easy inequality holds for every C*-algebra, including nonunital ones. -/
theorem minTensorNorm_le_maxTensorNorm (x : A ⊗[ℂ] C) :
    minTensorNorm.{0,0,0} x ≤ maxTensorNorm.{0,0,0} x := by
  apply csSup_le
  · exact ⟨_,scalarHilbert,scalarHilbert,0,0,rfl⟩
  · rintro _ ⟨H,K,R,S,rfl⟩
    rw [← completed_norm,completed_spatial_eq]
    exact norm_commutingEval_le x ⟨TensorHilbert H K⟩ (tensorLeftRep R) (tensorRightRep S)
      (tensor_reps_commute H K R S)

theorem maxTensorNorm_le_of_commuting (x : A ⊗[ℂ] C) (M : ℝ)
    (h : ∀ (H : ComplexHilbert.{0}) (R : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
      (S : C →⋆ₙₐ[ℂ] (H →L[ℂ] H)), (∀ a c, Commute (R a) (S c)) →
        ‖commutingEval H R S x‖ ≤ M) : maxTensorNorm.{0,0,0} x ≤ M := by
  apply csSup_le
  · refine ⟨_,scalarHilbert,0,0,?_,rfl⟩
    intro a c
    exact Commute.zero_left 0
  · rintro _ ⟨H,R,S,hRS,rfl⟩
    exact h H R S hRS
end Bounds
end NuclearUltrapower
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_CuntzNuclearity
attribute [-instance] _root_.OAI.NuclearUltrapower.VariableUltra.instCStarAlgebraAlgebra _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
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

/-- The actually constructed universal Cuntz algebra is nuclear in the full
spatial/commuting tensor-norm sense used in the obstruction theorem. -/
theorem CuntzUniversal.nuclear : IsNuclear.{0,0} CuntzUniversal.Algebra := by
  intro C inst x
  apply le_antisymm (minTensorNorm_le_maxTensorNorm x)
  apply maxTensorNorm_le_of_commuting
  intro H R S hRS
  exact CuntzAveraging.commutingEval_norm_le_min H R S hRS x

end NuclearUltrapower
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace NuclearUltrapower

/-- The exact source main theorem, including the explicitly stated Cuntz O₂
corollary. Both universal C*-algebras and the genuine nuclearity of O₂ have
been constructed; the target and free ultrafilter are arbitrary. -/
theorem main_no_embedding_oai : MainStatementWithCuntzCorollary.{0} := by
  obtain ⟨A,ι,hfull,hsep,hno⟩ := main_statement
  refine ⟨A,ι,hfull,hsep,hno,CuntzUniversal.bundled,CuntzUniversal.generator,
    CuntzUniversal.universal,?_⟩
  exact hno CuntzUniversal.bundled CuntzUniversal.nuclear

end NuclearUltrapower
end
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.main_no_embedding_oai := @OAI.NuclearUltrapower.main_no_embedding_oai
