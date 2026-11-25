-- Prove2me | solution 1 for GlobalTheory.HermWitt.witt_theorem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:48:53.673601+00:00
-- url     : https://prove2.me/submissions/51238dcd-cca8-4f24-8ec4-e92d2437c24c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Theorems.Thm_GlobalTheory_HermWitt_exists_gl_isometry_mulVec_eq
import Theorems.Thm_GlobalTheory_HermWitt_exists_gl_isometry_extend
import Theorems.Thm_GlobalTheory_HermWitt_congr_of_fromBlocks_congr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HermWitt
open Module Matrix GlobalTheory.HermDiag
namespace GlobalTheory.HermWitt
theorem _root_.solution {E : Type*} [Field E] (h2 : (2 : E) ≠ 0) (c : E →+* E)
    (hc : ∀ t, c (c t) = t) {r : ℕ} (G : Matrix (Fin r) (Fin r) E)
    (hG : ∀ a b, c (G a b) = G b a) :
    (∀ x y : Fin r → E, x ⬝ᵥ G *ᵥ (c ∘ x) = y ⬝ᵥ G *ᵥ (c ∘ y) → x ⬝ᵥ G *ᵥ (c ∘ x) ≠ 0 →
      ∃ γ : GL (Fin r) E,
        (∀ z w, ((γ : Matrix (Fin r) (Fin r) E) *ᵥ z) ⬝ᵥ G *ᵥ
          (c ∘ ((γ : Matrix (Fin r) (Fin r) E) *ᵥ w)) = z ⬝ᵥ G *ᵥ (c ∘ w)) ∧
        (γ : Matrix (Fin r) (Fin r) E) *ᵥ x = y) ∧
    (∀ {s : ℕ} (D : Matrix (Fin s) (Fin s) E), (∀ a b, c (D a b) = D b a) → D.det ≠ 0 →
      ∀ G' : Matrix (Fin r) (Fin r) E,
        (∃ P : Matrix (Fin s ⊕ Fin r) (Fin s ⊕ Fin r) E, P.det ≠ 0 ∧
          fromBlocks D 0 0 G' = Pᵀ * fromBlocks D 0 0 G * P.map c) →
        ∃ Q : Matrix (Fin r) (Fin r) E, Q.det ≠ 0 ∧ G' = Qᵀ * G * Q.map c) ∧
    (G.det ≠ 0 → ∀ (U U' : Submodule E (Fin r → E)) (f : U ≃ₗ[E] U'),
      (∀ a b : U, (f a : Fin r → E) ⬝ᵥ G *ᵥ (c ∘ (f b : Fin r → E)) =
        (a : Fin r → E) ⬝ᵥ G *ᵥ (c ∘ (b : Fin r → E))) →
      ∃ γ : GL (Fin r) E,
        (∀ z w, ((γ : Matrix (Fin r) (Fin r) E) *ᵥ z) ⬝ᵥ G *ᵥ
          (c ∘ ((γ : Matrix (Fin r) (Fin r) E) *ᵥ w)) = z ⬝ᵥ G *ᵥ (c ∘ w)) ∧
        ∀ a : U, (γ : Matrix (Fin r) (Fin r) E) *ᵥ (a : Fin r → E) = f a) := by
  refine ⟨fun x y hxy hx => ?_, fun D hD hdet G' ⟨P, hP, h⟩ => ?_, fun hdet U U' f hf => ?_⟩
  · obtain ⟨γ, h1, h3, -⟩ := exists_gl_isometry_mulVec_eq h2 hc hG hxy hx
    exact ⟨γ, h1, h3⟩
  · exact congr_of_fromBlocks_congr h2 hc hD hdet hG hP h
  · exact exists_gl_isometry_extend h2 hc hG hdet f hf
end GlobalTheory.HermWitt
