-- Prove2me | solution 1 for GlobalTheory.HermWitt.exists_gl_isometry_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:38:50.376653+00:00
-- url     : https://prove2.me/submissions/5c13cd4f-90ee-4ea6-bf61-f17337097bb1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Theorems.Thm_GlobalTheory_HermWitt_exists_isometry_comp_eq
import Theorems.Thm_GlobalTheory_HermWitt_eq_zero_of_forall_dotProduct_eq_zero
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
    {G : Matrix n n E} (hG : ∀ a b, c (G a b) = G b a) (hdet : G.det ≠ 0)
    {W : Type*} [AddCommGroup W] [Module E W] {g f : W →ₗ[E] (n → E)}
    (h0 : ∀ a, g a = 0 ↔ f a = 0)
    (hgf : ∀ a b, f a ⬝ᵥ G *ᵥ (c ∘ f b) = g a ⬝ᵥ G *ᵥ (c ∘ g b)) :
    ∃ γ : GL n E,
      (∀ z w, ((γ : Matrix n n E) *ᵥ z) ⬝ᵥ G *ᵥ (c ∘ ((γ : Matrix n n E) *ᵥ w)) =
        z ⬝ᵥ G *ᵥ (c ∘ w)) ∧ ∀ a, (γ : Matrix n n E) *ᵥ g a = f a := by
  obtain ⟨γ, hγ⟩ := exists_isometry_comp_eq h2 hc
    (B := Matrix.toLinearMapₛₗ₂' E (RingHom.id E) c G)
    (fun x y => by
      simp only [toLinearMapₛₗ₂'_eq_dotProduct, map_dotProduct_mulVec_comp hc hG])
    (fun x hx => eq_zero_of_forall_dotProduct_eq_zero hdet
      (by simpa only [toLinearMapₛₗ₂'_eq_dotProduct] using hx))
    (g := g) (f := f) h0 (by simpa only [toLinearMapₛₗ₂'_eq_dotProduct] using hgf)
  obtain ⟨g, hg⟩ := exists_gl_mulVec_eq γ
  exact ⟨g, by simpa only [toLinearMapₛₗ₂'_eq_dotProduct, hg] using hγ⟩
end GlobalTheory.HermWitt
