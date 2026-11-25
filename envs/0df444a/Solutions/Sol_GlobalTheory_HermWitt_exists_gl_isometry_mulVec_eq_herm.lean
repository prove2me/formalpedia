-- Prove2me | solution 1 for GlobalTheory.HermWitt.exists_gl_isometry_mulVec_eq_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:48:43.97962+00:00
-- url     : https://prove2.me/submissions/913b189f-12c3-4dae-b05b-6c80cb806f42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Theorems.Thm_GlobalTheory_HermWitt_exists_gl_isometry_mulVec_eq
import Theorems.Thm_GlobalTheory_HermDiag_herm_eq_dotProduct


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
open NumberField ReciprocityTheory.ChartRestriction.G
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.HermWitt
theorem _root_.solution {G : Matrix (Fin r) (Fin r) E}
    (hG : ∀ a b, FD.cc (G a b) = G b a) {x y : Fin r → E}
    (hxy : FD.herm G x x = FD.herm G y y) (hx : FD.herm G x x ≠ 0) :
    ∃ γ : GL (Fin r) E,
      (∀ z w, FD.herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ z)
        ((γ : Matrix (Fin r) (Fin r) E) *ᵥ w) = FD.herm G z w) ∧
      (γ : Matrix (Fin r) (Fin r) E) *ᵥ x = y ∧
      ∀ u, FD.herm G u x = 0 → FD.herm G u y = 0 → (γ : Matrix (Fin r) (Fin r) E) *ᵥ u = u := by
  simp only [herm_eq_dotProduct] at hxy hx ⊢
  exact exists_gl_isometry_mulVec_eq (c := (IsCMField.complexConj E : E →+* E))
    two_ne_zero (IsCMField.complexConj_apply_apply E) hG hxy hx
end GlobalTheory.HermWitt
