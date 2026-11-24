-- Prove2me | solution 1 for GlobalTheory.HermWitt.exists_isometry_of_graph
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:02:57.811926+00:00
-- url     : https://prove2.me/submissions/f601635f-a082-4240-8bf9-f0b17ac23596

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Theorems.Thm_GlobalTheory_HermWitt_exists_isometry_comp_eq_of_nondegenerate
import Theorems.Thm_GlobalTheory_HermWitt_exists_graph_lt

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
    (hV : ∀ x, (∀ y, B y x = 0) → x = 0) (Γ : Submodule E (V × V))
    (h0 : ∀ p ∈ Γ, p.1 = 0 ↔ p.2 = 0) (hΓ : ∀ p ∈ Γ, ∀ q ∈ Γ, B p.2 q.2 = B p.1 q.1) :
    ∃ γ : V ≃ₗ[E] V, (∀ z w, B (γ z) (γ w) = B z w) ∧ ∀ p ∈ Γ, γ p.1 = p.2 := by
  induction Γ using WellFoundedGT.induction with
  | ind Γ ih =>
    by_cases h : ∃ r ∈ Γ, r ≠ 0 ∧ ∀ p ∈ Γ, B p.1 r.1 = 0
    · obtain ⟨r, hr, hr0, hrad⟩ := h
      obtain ⟨Γ', hlt, h0', hΓ'⟩ := exists_graph_lt h2 hc hB hV Γ h0 hΓ hr hr0 hrad
      obtain ⟨γ, hγ, e⟩ := ih Γ' hlt h0' hΓ'
      exact ⟨γ, hγ, fun p hp => e p (hlt.le hp)⟩
    · obtain ⟨γ, hγ, e⟩ := exists_isometry_comp_eq_of_nondegenerate h2 hB
        (g := LinearMap.fst E V V ∘ₗ Γ.subtype) (f := LinearMap.snd E V V ∘ₗ Γ.subtype)
        (fun a b => hΓ a a.2 b b.2)
        (fun a ha => by
          by_contra hne
          exact h ⟨a, a.2, fun h' => hne (Subtype.ext h'), fun p hp => ha ⟨p, hp⟩⟩)
      exact ⟨γ, hγ, fun p hp => e ⟨p, hp⟩⟩
end GlobalTheory.HermWitt
