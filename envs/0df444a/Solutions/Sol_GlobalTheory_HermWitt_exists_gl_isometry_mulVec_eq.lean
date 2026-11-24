-- Prove2me | solution 1 for GlobalTheory.HermWitt.exists_gl_isometry_mulVec_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:48.146852+00:00
-- url     : https://prove2.me/submissions/945ad8fd-4b88-4683-8d28-cf223337adb0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Theorems.Thm_GlobalTheory_HermWitt_exists_isometry_apply_eq
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
    {G : Matrix n n E} (hG : ∀ a b, c (G a b) = G b a) {x y : n → E}
    (hxy : x ⬝ᵥ G *ᵥ (c ∘ x) = y ⬝ᵥ G *ᵥ (c ∘ y)) (hx : x ⬝ᵥ G *ᵥ (c ∘ x) ≠ 0) :
    ∃ γ : GL n E,
      (∀ z w, ((γ : Matrix n n E) *ᵥ z) ⬝ᵥ G *ᵥ (c ∘ ((γ : Matrix n n E) *ᵥ w)) =
        z ⬝ᵥ G *ᵥ (c ∘ w)) ∧ (γ : Matrix n n E) *ᵥ x = y ∧
      ∀ u, u ⬝ᵥ G *ᵥ (c ∘ x) = 0 → u ⬝ᵥ G *ᵥ (c ∘ y) = 0 → (γ : Matrix n n E) *ᵥ u = u := by
  obtain ⟨γ, hγ⟩ := exists_isometry_apply_eq h2
    (B := Matrix.toLinearMapₛₗ₂' E (RingHom.id E) c G)
    (fun x y => by
      simp only [toLinearMapₛₗ₂'_eq_dotProduct, map_dotProduct_mulVec_comp hc hG])
    (x := x) (y := y) (by simpa only [toLinearMapₛₗ₂'_eq_dotProduct] using hxy)
    (by simpa only [toLinearMapₛₗ₂'_eq_dotProduct] using hx)
  obtain ⟨g, hg⟩ := exists_gl_mulVec_eq γ
  exact ⟨g, by simpa only [toLinearMapₛₗ₂'_eq_dotProduct, hg] using hγ⟩
end GlobalTheory.HermWitt
