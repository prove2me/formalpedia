-- Prove2me | solution 1 for OAI.NuclearUltrapower.injectiveInduced_invariant_tensor
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T14:34:22.743545+00:00
-- url     : https://prove2.me/submissions/653bdd35-df54-457f-9c4c-279944a5fca2

import Mathlib
import Definitions.Def_OAIQ019N043

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_HilbertInduction
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzWords.instDecidableEqWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.VariableUltra.instCStarAlgebraAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAddCommGroupAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedRingAlgebra _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped ENNReal InnerProductSpace
namespace NuclearUltrapower
universe u v

section Induction
variable {G : Type u} [Group G] (H : Subgroup G)

variable {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  (α : H →* (V ≃ₗᵢ[ℂ] V))

theorem inductionInclusion_intertwines (h : H) (v : V) :
    inductionInclusion H (α h v) = inducedUnitary H α (h:G) (inductionInclusion H v) := by
  classical
  ext i
  by_cases hi : i = (QuotientGroup.mk 1 : G ⧸ H)
  · subst i
    rw [induced_identity_coordinate]
    simp
  · have hh : (h:G)⁻¹ • i ≠ (QuotientGroup.mk 1 : G ⧸ H) := by
      intro he
      have := congrArg (fun j : G ⧸ H => (h:G) • j) he
      exact hi (by simpa only [smul_inv_smul, subgroup_smul_identity] using this)
    simp only [inductionInclusion_apply, Pi.single_eq_of_ne hi, inducedUnitary_apply,
      Pi.single_eq_of_ne hh, map_zero]

end Induction
end NuclearUltrapower
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_Schur
attribute [-instance] _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAddCommGroupAlgebra _root_.OAI.NuclearUltrapower.lp_finiteDimensional
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
namespace NuclearUltrapower

open scoped TensorProduct
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable {Γ : Type u} [Group Γ]

section MixedTensor
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Tensor invariance is the genuine intertwining equation. -/
theorem mixedTensorOperator_action (u : E ≃ₗᵢ[ℂ] E) (v : F ≃ₗᵢ[ℂ] F)
    (z : E ⊗[ℂ] StrongDual ℂ F) :
    mixedTensorOperator (TensorProduct.congrIsometry u (dualUnitary v) z) =
      (u : E →L[ℂ] E).comp ((mixedTensorOperator z).comp (v.symm : F →L[ℂ] F)) := by
  induction z using OAI.tensorInductionOn with
  | tmul x f => ext y; simp
  | add x y hx hy => simp only [map_add, hx, hy, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]

end MixedTensor

end NuclearUltrapower

namespace NuclearUltrapower
open scoped TensorProduct
section TensorSurjective
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] [CompleteSpace F]

/-- Every operator with finite-dimensional domain is represented by an actual
algebraic tensor; no completed-tensor compactness argument is hidden here. -/
theorem mixedTensorOperator_surjective :
    Function.Surjective (mixedTensorOperator (E := E) (F := F)) := by
  intro T
  let b := stdOrthonormalBasis ℂ F
  refine ⟨∑ i, T (b i) ⊗ₜ[ℂ] InnerProductSpace.toDual ℂ F (b i), ?_⟩
  apply ContinuousLinearMap.ext
  intro x
  simp only [map_sum, sum_apply, mixedTensorOperator_tmul]
  change (∑ i, inner ℂ (b i) x • T (b i)) = T x
  calc
    _ = T (∑ i, inner ℂ (b i) x • b i) := by simp only [map_sum, map_smul]
    _ = T x := congrArg T (b.sum_repr' x)

/-- A nonzero finite-dimensional intertwiner gives a nonzero invariant tensor. -/
theorem exists_invariant_tensor_of_intertwiner {Γ : Type*} [Group Γ]
    (ρ : Γ →* (E ≃ₗᵢ[ℂ] E)) (π : Γ →* (F ≃ₗᵢ[ℂ] F))
    (T : F →L[ℂ] E) (hT : T ≠ 0)
    (hcomm : ∀ g x, T (π g x) = ρ g (T x)) :
    ∃ z : E ⊗[ℂ] StrongDual ℂ F, z ≠ 0 ∧
      ∀ g, tensorContragredientRep ρ π g z = z := by
  obtain ⟨z, hz⟩ := mixedTensorOperator_surjective (E := E) T
  refine ⟨z, ?_, ?_⟩
  · intro h0
    apply hT
    simpa only [h0, map_zero] using hz.symm
  · intro g
    apply mixedTensorOperator_injective
    change mixedTensorOperator (TensorProduct.congrIsometry (ρ g) (dualUnitary (π g)) z) = _
    rw [mixedTensorOperator_action, hz]
    apply ContinuousLinearMap.ext
    intro x
    change ρ g (T ((π g).symm x)) = T x
    rw [← hcomm, (π g).apply_symm_apply]
end TensorSurjective

end NuclearUltrapower

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_GroupObstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped TensorProduct InnerProductSpace
namespace NuclearUltrapower
universe u v w
section InjectiveInduction
variable {Γ : Type u} {Δ : Type v} [Group Γ] [Group Δ]
  (f : Γ →* Δ) (hf : Function.Injective f) (π : FiniteUnitaryRep.{u,w} Γ)

/-- On the identity coset the induced representation contains the original one. -/
theorem injectiveInduction_intertwines (g : Γ) (x : π) :
    inductionInclusion f.range (π.action g x) =
      injectiveInduced f hf π (f g) (inductionInclusion f.range x) := by
  have h := inductionInclusion_intertwines f.range
    (π.action.comp (MonoidHom.ofInjective hf).symm.toMonoidHom)
    ((MonoidHom.ofInjective hf) g) x
  simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply, MonoidHom.ofInjective_apply, injectiveInduced] using h

/-- The full group algebra sees the initial finite-dimensional constituent,
using an algebraic invariant tensor in the identity coset of the induction. -/
theorem injectiveInduced_invariant_tensor_oai :
    ∃ z : InjectiveInducedSpace f π ⊗[ℂ] π.dual, z ≠ 0 ∧
      ∀ g : Γ, TensorProduct.congrIsometry (injectiveInduced f hf π (f g))
        (π.dual.action g) z = z := by
  let T : π →L[ℂ] InjectiveInducedSpace f π := (inductionInclusion f.range).toContinuousLinearMap
  have hT : T ≠ 0 := by
    intro h
    obtain ⟨x,hx⟩ := exists_ne (0 : π)
    apply hx
    apply (inductionInclusion f.range).injective
    rw [map_zero]
    exact congrArg (fun T : π →L[ℂ] InjectiveInducedSpace f π => T x) h
  obtain ⟨z,hz,hiz⟩ := exists_invariant_tensor_of_intertwiner
    ((injectiveInduced f hf π).comp f) π.action T hT
    (injectiveInduction_intertwines f hf π)
  exact ⟨z,hz,hiz⟩

end InjectiveInduction
end NuclearUltrapower
end
end

end OAI
end

theorem solution.{u, v, w} : type_of% @OAI.NuclearUltrapower.injectiveInduced_invariant_tensor_oai.{u, v, w} := @OAI.NuclearUltrapower.injectiveInduced_invariant_tensor_oai.{u, v, w}
