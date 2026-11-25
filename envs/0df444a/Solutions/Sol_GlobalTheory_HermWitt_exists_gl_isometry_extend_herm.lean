-- Prove2me | solution 1 for GlobalTheory.HermWitt.exists_gl_isometry_extend_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:48:39.248335+00:00
-- url     : https://prove2.me/submissions/02c4d032-3d7b-4802-8563-17f65cd654d5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Theorems.Thm_GlobalTheory_HermWitt_exists_gl_isometry_extend
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
    (hG : ∀ a b, FD.cc (G a b) = G b a) (hdet : G.det ≠ 0)
    {U U' : Submodule E (Fin r → E)} (f : U ≃ₗ[E] U')
    (hf : ∀ a b : U, FD.herm G (f a) (f b) = FD.herm G a b) :
    ∃ γ : GL (Fin r) E,
      (∀ z w, FD.herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ z)
        ((γ : Matrix (Fin r) (Fin r) E) *ᵥ w) = FD.herm G z w) ∧
      ∀ a : U, (γ : Matrix (Fin r) (Fin r) E) *ᵥ (a : Fin r → E) = f a := by
  simp only [herm_eq_dotProduct] at hf ⊢
  exact exists_gl_isometry_extend (c := (IsCMField.complexConj E : E →+* E))
    two_ne_zero (IsCMField.complexConj_apply_apply E) hG hdet f hf
end GlobalTheory.HermWitt
