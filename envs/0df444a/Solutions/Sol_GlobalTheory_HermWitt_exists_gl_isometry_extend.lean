-- Prove2me | solution 1 for GlobalTheory.HermWitt.exists_gl_isometry_extend
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:54:10.551019+00:00
-- url     : https://prove2.me/submissions/80ec0cf3-1296-453c-8ae8-eae040f7a4a9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Theorems.Thm_GlobalTheory_HermWitt_exists_gl_isometry_comp_eq

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
    {U U' : Submodule E (n → E)} (f : U ≃ₗ[E] U')
    (hf : ∀ a b : U, (f a : n → E) ⬝ᵥ G *ᵥ (c ∘ (f b : n → E)) =
      (a : n → E) ⬝ᵥ G *ᵥ (c ∘ (b : n → E))) :
    ∃ γ : GL n E,
      (∀ z w, ((γ : Matrix n n E) *ᵥ z) ⬝ᵥ G *ᵥ (c ∘ ((γ : Matrix n n E) *ᵥ w)) =
        z ⬝ᵥ G *ᵥ (c ∘ w)) ∧ ∀ a : U, (γ : Matrix n n E) *ᵥ (a : n → E) = f a :=
  exists_gl_isometry_comp_eq h2 hc hG hdet (g := U.subtype) (f := U'.subtype ∘ₗ f.toLinearMap)
    (fun a => by simp) hf
end GlobalTheory.HermWitt
