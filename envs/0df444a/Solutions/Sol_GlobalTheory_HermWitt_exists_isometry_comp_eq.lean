-- Prove2me | solution 1 for GlobalTheory.HermWitt.exists_isometry_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:24:28.456798+00:00
-- url     : https://prove2.me/submissions/e4403295-fc40-446d-ad08-92c7928a0c30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Theorems.Thm_GlobalTheory_HermWitt_exists_isometry_of_graph

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
    (hV : ∀ x, (∀ y, B y x = 0) → x = 0) {W : Type*} [AddCommGroup W] [Module E W]
    {g f : W →ₗ[E] V} (h0 : ∀ a, g a = 0 ↔ f a = 0)
    (hgf : ∀ a b, B (f a) (f b) = B (g a) (g b)) :
    ∃ γ : V ≃ₗ[E] V, (∀ z w, B (γ z) (γ w) = B z w) ∧ ∀ a, γ (g a) = f a := by
  obtain ⟨γ, hγ, e⟩ := exists_isometry_of_graph h2 hc hB hV (LinearMap.range (g.prod f))
    (by rintro _ ⟨a, rfl⟩; exact h0 a) (by rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩; exact hgf a b)
  exact ⟨γ, hγ, fun a => e _ ⟨a, rfl⟩⟩
end GlobalTheory.HermWitt
