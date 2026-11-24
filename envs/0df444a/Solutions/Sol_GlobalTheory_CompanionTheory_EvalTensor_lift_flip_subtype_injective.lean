-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.EvalTensor.lift_flip_subtype_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:47:06.256379+00:00
-- url     : https://prove2.me/submissions/bdded210-f980-48e8-aefd-87c037c09285

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_EqZeroOfSumApplyEqZero
import Theorems.Thm_GlobalTheory_CompanionTheory_EvalTensor_eq_zero_of_sum_apply_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.EvalTensor
variable {G S V : Type} [Group G] [AddCommGroup S] [Module ℂ S] [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.CompanionTheory.EvalTensor
theorem _root_.solution : ∀ {G S V : Type} [Group G] [AddCommGroup S] [Module ℂ S] [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ G S) (π : Representation ℂ G V), σ.IsIrreducible → (∀ A : S →ₗ[ℂ] S, (∀ g s, A (σ g s) = σ g (A s)) → ∃ c : ℂ, A = c • LinearMap.id) → ∀ M : Submodule ℂ (S →ₗ[ℂ] V), (∀ f ∈ M, ∀ g s, f (σ g s) = π g (f s)) → Function.Injective (TensorProduct.lift (LinearMap.flip (M.subtype)) : S ⊗[ℂ] M →ₗ[ℂ] V) := by
  intro G S V _ _ _ _ _ σ π hirr hschur M hM
  classical
  let β := Module.Basis.ofVectorSpace ℂ M
  have hli : LinearIndependent ℂ (fun i => ((β i : M) : S →ₗ[ℂ] V)) :=
    β.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  rw [injective_iff_map_eq_zero]
  intro x hx
  let E := TensorProduct.equivFinsuppOfBasisRight (M := S) β
  have hxs : x = (E x).sum fun i s => s ⊗ₜ[ℂ] β i := by
    rw [← TensorProduct.equivFinsuppOfBasisRight_symm_apply, LinearEquiv.symm_apply_apply]
  have hsum : ∑ i ∈ (E x).support, ((β i : M) : S →ₗ[ℂ] V) (E x i) = 0 := by
    rw [hxs, Finsupp.sum, map_sum] at hx
    simpa using hx
  have h0 := eq_zero_of_sum_apply_eq_zero σ π hirr hschur _ hli
    (fun i g s => hM _ (β i).2 g s) (E x).support (fun i => E x i) hsum
  have hE : E x = 0 := by
    ext i
    by_cases hi : i ∈ (E x).support
    · simpa using h0 i hi
    · simpa using hi
  exact E.map_eq_zero_iff.1 hE
end GlobalTheory.CompanionTheory.EvalTensor
