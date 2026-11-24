-- Prove2me | solution 1 for GlobalTheory.InfAdeleCM.infAdele_tensor_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:22:09.632951+00:00
-- url     : https://prove2.me/submissions/8ad4d711-9d67-4772-8411-f7d0c12d0829

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_InfAdeleTensorBijective
import Theorems.Thm_GlobalTheory_InfAdeleCM_conj_ext
import Theorems.Thm_GlobalTheory_InfAdeleCM_exists_hom
import Theorems.Thm_GlobalTheory_InfAdeleCM_hom_tmul
import Theorems.Thm_GlobalTheory_InfAdeleCM_bijective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Topology Matrix
open GlobalTheory GlobalTheory.InfAdeleCM
variable {F : Type} [Field F] [NumberField F]
variable {E : Type} [Field E] [NumberField E] [Algebra F E]
namespace GlobalTheory.InfAdeleCM
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E), Module.finrank F E = 2 → c ≠ 1 → IsTotallyReal F → (∀ (τ : E →+* ℂ) x, τ (c x) = starRingEnd ℂ (τ x)) → letI : TopologicalSpace (InfiniteAdeleRing F ⊗[F] E) := moduleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E); (∀ τ : E →+* ℂ, ∃ θ : InfiniteAdeleRing F ⊗[F] E →+* ℂ, (∀ x, θ (1 ⊗ₜ x) = τ x) ∧ Continuous fun a : InfiniteAdeleRing F => θ (a ⊗ₜ (1 : E))) ∧ ∀ θ : (E →+* ℂ) → (InfiniteAdeleRing F ⊗[F] E →+* ℂ), (∀ τ, (∀ x, θ τ (1 ⊗ₜ x) = τ x) ∧ Continuous fun a : InfiniteAdeleRing F => θ τ (a ⊗ₜ (1 : E))) → (∀ τ, Continuous (θ τ)) ∧ (∀ τ z, θ τ (sg (InfiniteAdeleRing F) c z) = starRingEnd ℂ (θ τ z)) ∧ ∀ Ψ : Set (E →+* ℂ), (∀ τ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) → Function.Bijective (fun (z : InfiniteAdeleRing F ⊗[F] E) (τ : Ψ) => θ τ.1 z) := by
  intro F E _ _ _ _ _ c h2 hc hF hτ
  letI : TopologicalSpace (InfiniteAdeleRing F ⊗[F] E) :=
    moduleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E)
  haveI : IsModuleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E) := ⟨rfl⟩
  refine ⟨exists_hom, fun θ hθ => ?_⟩
  have hθ' := fun τ => hom_tmul τ (θ τ) (hθ τ).1 (hθ τ).2
  refine ⟨fun τ => ?_, fun τ z => ?_, bijective c h2 hc hτ θ hθ'⟩
  · exact IsModuleTopology.continuous_of_ringHom (R := InfiniteAdeleRing F) (θ τ) (hθ τ).2
  · induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      simp only [sg, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id, hθ', map_mul, conj_ext]
      rw [← hτ]
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]
end GlobalTheory.InfAdeleCM
