-- Prove2me | solution 1 for GlobalTheory.HermGram.gram_posDef_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:01:25.958947+00:00
-- url     : https://prove2.me/submissions/a944f7ca-6419-44f9-8754-5bd0478f2301

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PosDefRealGramPairHermitianForms
import Theorems.Thm_GlobalTheory_HermGram_reForm_apply
import Theorems.Thm_GlobalTheory_HermGram_gram_posDef

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.HermGram
namespace GlobalTheory.HermGram
theorem _root_.solution (g n : ℕ) (e : Module.Basis (Fin n) ℝ (Fin g → ℂ)) (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ)
    (h₁ : H₁.IsHermitian) (h₂ : H₂.IsHermitian)
    (p₁ : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₁.mulVec (star z)).re)
    (p₂ : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₂.mulVec (star z)).re)
    (γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hγ : ∀ z w, z ⬝ᵥ H₂.mulVec (star w) = z ⬝ᵥ H₁.mulVec (star (γ w))) :
    (Matrix.of fun k l => (e k ⬝ᵥ H₁.mulVec (star (e l))).re).PosDef ∧
    ((Matrix.of fun k l => (e k ⬝ᵥ H₁.mulVec (star (e l))).re) *
      LinearMap.toMatrix e e (γ.restrictScalars ℝ)).PosDef := by
  refine ⟨gram_posDef e h₁ p₁, ?_⟩
  have hG : (Matrix.of fun k l => (e k ⬝ᵥ H₁.mulVec (star (e l))).re) *
      LinearMap.toMatrix e e (γ.restrictScalars ℝ) =
      Matrix.of fun k l => (e k ⬝ᵥ H₂.mulVec (star (e l))).re := by
    ext k l
    rw [of_apply, hγ, mul_apply]
    have hs : γ (e l) = ∑ m, e.repr (γ (e l)) m • e m := (e.sum_repr _).symm
    have : (e k ⬝ᵥ H₁.mulVec (star (γ (e l)))).re = reForm H₁ (e k) (γ (e l)) := rfl
    rw [this, hs]
    simp only [map_sum, map_smul, smul_eq_mul, LinearMap.toMatrix_apply, of_apply,
      LinearMap.restrictScalars_apply, reForm_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  rw [hG]
  exact gram_posDef e h₂ p₂
end GlobalTheory.HermGram
