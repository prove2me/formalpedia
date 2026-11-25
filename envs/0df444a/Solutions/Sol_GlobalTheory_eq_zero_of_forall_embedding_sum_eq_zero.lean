-- Prove2me | solution 1 for GlobalTheory.eq_zero_of_forall_embedding_sum_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:22:21.273278+00:00
-- url     : https://prove2.me/submissions/3b8b4eb4-ef14-473d-891d-090a6e7b851b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_EqZeroOfForallEmbeddingSumEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (K K₁ : Type) [Field K] [CharZero K] [Field K₁] [Algebra K K₁] [FiniteDimensional K K₁] (σ₀ : K →+* ℂ) (n : ℕ) (e : Fin n → ℂ) (y : Fin n → K₁), (∀ c : Fin n → K, ∑ b, σ₀ (c b) * e b = 0 → c = 0) → (∀ σ₁ : K₁ →+* ℂ, σ₁.comp (algebraMap K K₁) = σ₀ → ∑ b, e b * σ₁ (y b) = 0) → y = 0 := by
  intro K K₁ _ _ _ _ _ σ₀ n e y hind hrel
  classical
  letI : Algebra K ℂ := σ₀.toAlgebra
  have hσ : ∀ x : K, algebraMap K ℂ x = σ₀ x := fun _ => rfl
  let ω := Module.finBasis K K₁
  have hcard : Fintype.card (Fin (Module.finrank K K₁)) = Fintype.card (K₁ →ₐ[K] ℂ) := by
    rw [AlgHom.card, Fintype.card_fin]
  let ε : Fin (Module.finrank K K₁) ≃ (K₁ →ₐ[K] ℂ) := Fintype.equivOfCardEq hcard
  have hd := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two K ℂ ω ε
  have hd0 : Algebra.discr K ω ≠ 0 := Algebra.discr_not_zero_of_basis K ω
  have hdet : (Algebra.embeddingsMatrixReindex K ℂ ω ε).det ≠ 0 := by
    intro h
    rw [h, zero_pow two_ne_zero] at hd
    exact hd0 ((algebraMap K ℂ).injective (by rw [hd, map_zero]))
  let u : Fin (Module.finrank K K₁) → ℂ := fun s => ∑ b, σ₀ (ω.repr (y b) s) * e b
  have hu : u = 0 := by
    apply Matrix.eq_zero_of_vecMul_eq_zero hdet
    funext j
    have h1 := hrel (ε j : K₁ →+* ℂ) (by
      ext x
      simp [hσ])
    have h2 : ∀ b, (ε j : K₁ →+* ℂ) (y b) = ∑ s, σ₀ (ω.repr (y b) s) * ε j (ω s) := by
      intro b
      conv_lhs => rw [← ω.sum_repr (y b)]
      simp only [RingHom.coe_coe, map_sum, Algebra.smul_def, map_mul, AlgHom.commutes, hσ]
    simp only [h2, Finset.mul_sum] at h1
    rw [Finset.sum_comm] at h1
    simp only [Matrix.vecMul, dotProduct, u, Finset.sum_mul, Pi.zero_apply]
    rw [← h1]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun b _ => ?_
    have : Algebra.embeddingsMatrixReindex K ℂ ω ε s j = ε j (ω s) := by
      simp [Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix]
    rw [this]; ring
  funext b
  apply ω.repr.injective
  ext s
  have := congrFun (hind (fun b => ω.repr (y b) s) (congrFun hu s)) b
  simpa using this
end GlobalTheory
