-- Prove2me | solution 1 for GlobalTheory.HermWitt.exists_gl_isometry_comp_eq_of_nondegenerate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:36:28.477598+00:00
-- url     : https://prove2.me/submissions/e2076428-6b47-49f0-99dc-700fa6e9ab9b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Theorems.Thm_GlobalTheory_HermWitt_exists_isometry_comp_eq_of_nondegenerate
import Theorems.Thm_GlobalTheory_HermWitt_exists_gl_mulVec_eq
import Theorems.Thm_GlobalTheory_HermDiag_map_dotProduct_mulVec_comp
import Theorems.Thm_P2M_GlobalTheory_HermDiag_toLinearMap_____eq_dotProduct_72a26b3ab9da


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
variable {E : Type*} [Field E] {c : E →+* E} {n : Type*} [Fintype n] [DecidableEq n]
namespace GlobalTheory.HermWitt
theorem _root_.solution (h2 : (2 : E) ≠ 0) (hc : ∀ t, c (c t) = t)
    {G : Matrix n n E} (hG : ∀ a b, c (G a b) = G b a) {W : Type*} [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] {g f : W →ₗ[E] (n → E)}
    (hgf : ∀ a b, f a ⬝ᵥ G *ᵥ (c ∘ f b) = g a ⬝ᵥ G *ᵥ (c ∘ g b))
    (hW : ∀ a, (∀ b, g b ⬝ᵥ G *ᵥ (c ∘ g a) = 0) → a = 0) :
    ∃ γ : GL n E,
      (∀ z w, ((γ : Matrix n n E) *ᵥ z) ⬝ᵥ G *ᵥ (c ∘ ((γ : Matrix n n E) *ᵥ w)) =
        z ⬝ᵥ G *ᵥ (c ∘ w)) ∧ ∀ a, (γ : Matrix n n E) *ᵥ g a = f a := by
  obtain ⟨γ, hγ⟩ := exists_isometry_comp_eq_of_nondegenerate h2
    (B := Matrix.toLinearMapₛₗ₂' E (RingHom.id E) c G)
    (fun x y => by
      simp only [toLinearMapₛₗ₂'_eq_dotProduct, map_dotProduct_mulVec_comp hc hG])
    (g := g) (f := f) (by simpa only [toLinearMapₛₗ₂'_eq_dotProduct] using hgf)
    (by simpa only [toLinearMapₛₗ₂'_eq_dotProduct] using hW)
  obtain ⟨g, hg⟩ := exists_gl_mulVec_eq γ
  exact ⟨g, by simpa only [toLinearMapₛₗ₂'_eq_dotProduct, hg] using hγ⟩
end GlobalTheory.HermWitt
