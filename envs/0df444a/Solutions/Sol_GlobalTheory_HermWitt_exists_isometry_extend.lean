-- Prove2me | solution 1 for GlobalTheory.HermWitt.exists_isometry_extend
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:48:48.358296+00:00
-- url     : https://prove2.me/submissions/27220c31-fe1f-4cbc-a690-400e39436433

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Theorems.Thm_GlobalTheory_HermWitt_exists_isometry_comp_eq

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
variable {E : Type*} [Field E] {c : E →+* E} {V : Type*} [AddCommGroup V] [Module E V]
namespace GlobalTheory.HermWitt
theorem _root_.solution [FiniteDimensional E V] (h2 : (2 : E) ≠ 0)
    (hc : ∀ t, c (c t) = t) {B : V →ₗ[E] V →ₛₗ[c] E} (hB : ∀ x y, c (B x y) = B y x)
    (hV : ∀ x, (∀ y, B y x = 0) → x = 0) {U U' : Submodule E V} (f : U ≃ₗ[E] U')
    (hf : ∀ a b : U, B (f a) (f b) = B a b) :
    ∃ γ : V ≃ₗ[E] V, (∀ z w, B (γ z) (γ w) = B z w) ∧ ∀ a : U, γ a = f a :=
  exists_isometry_comp_eq h2 hc hB hV (g := U.subtype) (f := U'.subtype ∘ₗ f.toLinearMap)
    (fun a => by simp) hf
end GlobalTheory.HermWitt
