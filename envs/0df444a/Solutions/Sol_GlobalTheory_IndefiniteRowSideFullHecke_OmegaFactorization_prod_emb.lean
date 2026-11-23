-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.prod_emb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:49:45.122367+00:00
-- url     : https://prove2.me/submissions/f6bcacb4-d620-4379-87fd-34e445221de2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
variable (F : Type) [Field F] [NumberField F]
variable {F}
open NumberField Complex
open scoped nonZeroDivisors ContDiff
variable (F : Type) [Field F] [NumberField F]
variable {F}
namespace GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
namespace _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
theorem _root_.solution [IsTotallyReal F] (x : F) :
    ∏ τ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, ((τ x : ℝ) : ℂ) = ((Algebra.norm ℚ x : ℚ) : ℂ) := by
  have h1 := Algebra.norm_eq_prod_embeddings ℚ ℂ x
  rw [eq_ratCast] at h1
  rw [h1]
  have h2 : ∏ σ : F →ₐ[ℚ] ℂ, σ x = ∏ φ : F →+* ℂ, φ x :=
    Fintype.prod_bijective (fun σ : F →ₐ[ℚ] ℂ => (σ : F →+* ℂ))
      (RingHom.equivRatAlgHom F ℂ).symm.bijective _ _ (fun _ => rfl)
  have h3 : ∏ τ : F →+* ℝ, ((τ x : ℝ) : ℂ) = ∏ φ : F →+* ℂ, φ x := by
    refine Fintype.prod_bijective (fun τ : F →+* ℝ => Complex.ofRealHom.comp τ) ⟨?_, ?_⟩ _ _
      (fun _ => rfl)
    · intro a b h
      ext y
      have := congrArg (fun f : F →+* ℂ => f y) h
      simpa using this
    · intro φ
      have hφ : ComplexEmbedding.IsReal φ :=
        InfinitePlace.isReal_mk_iff.mp (IsTotallyReal.isReal _)
      exact ⟨hφ.embedding, by ext y; simp [ComplexEmbedding.IsReal.coe_embedding_apply]⟩
  rw [h2, h3]
end _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
end GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
