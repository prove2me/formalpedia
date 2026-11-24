-- Prove2me | solution 1 for GlobalTheory.reducePoint_quotient_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:40:35.111826+00:00
-- url     : https://prove2.me/submissions/211d1b38-ad46-4768-816f-8885ae9afa46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsCompletionPointClosedPointMemOfSmooth
import Theorems.Thm_GlobalTheory_range_subset_opens_of_isLocalRing
import Theorems.Thm_GlobalTheory_exists_isAffineOpen_pair
import Theorems.Thm_GlobalTheory_exists_lift_of_smooth_of_isAffineOpen
import Theorems.Thm_GlobalTheory_exists_algHom_lift_of_smooth
import Theorems.Thm_GlobalTheory_isLocalRing_of_surjective_of_henselian


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S)
variable (B : Type u) [CommRing B] [IsLocalRing B] (I : Ideal B) [HenselianRing B I]
  (s : Spec (.of B) ⟶ S)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
variable {X S : Scheme.{u}} (f : X ⟶ S)
variable (B : Type u) [CommRing B] [IsLocalRing B] (I : Ideal B) [HenselianRing B I]
  (s : Spec (.of B) ⟶ S)
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution [Smooth f] :
    Function.Surjective (_root_.GlobalTheory.reducePoint f (CommRingCat.ofHom (Ideal.Quotient.mk I)) s) := by
  rintro ⟨x₀, hx₀⟩
  have hker : ∀ b : B, b ∈ I ↔ Ideal.Quotient.mk I b = 0 := fun b =>
    Ideal.Quotient.eq_zero_iff_mem.symm
  haveI : IsLocalRing (B ⧸ I) := _root_.GlobalTheory.isLocalRing_of_surjective_of_henselian I
    (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective hker
  haveI : IsLocalRing (CommRingCat.of (B ⧸ I)) := ‹IsLocalRing (B ⧸ I)›
  have hclosed : (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).base
      (closedPoint (CommRingCat.of (B ⧸ I))) = closedPoint B := by
    apply PrimeSpectrum.ext
    show Ideal.comap (Ideal.Quotient.mk I) (maximalIdeal (B ⧸ I)) = maximalIdeal B
    exact IsLocalRing.eq_maximalIdeal
      (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
  obtain ⟨U, V, hU, hV, hVU, -, hxV⟩ :=
    _root_.GlobalTheory.exists_isAffineOpen_pair f (x₀ (closedPoint (CommRingCat.of (B ⧸ I)))) (O := ⊤) trivial
  have hfx : f (x₀ (closedPoint (CommRingCat.of (B ⧸ I)))) = s (closedPoint B) := by
    change (x₀ ≫ f).base _ = _
    rw [hx₀]
    exact congrArg s.base hclosed
  have hs : Set.range s ⊆ U := _root_.GlobalTheory.range_subset_opens_of_isLocalRing s (hfx ▸ hVU hxV)
  have hx : Set.range x₀ ⊆ V := _root_.GlobalTheory.range_subset_opens_of_isLocalRing x₀ hxV
  obtain ⟨x, hπx, hxf⟩ := _root_.GlobalTheory.exists_lift_of_smooth_of_isAffineOpen f hU hV hVU _ s x₀ hx₀ hs hx
    (fun R A _ _ _ _ _ _ π' hπ' φ =>
      _root_.GlobalTheory.exists_algHom_lift_of_smooth I π'
        (fun c => by
          obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
          exact ⟨b, hπ' b⟩)
        (fun b => by rw [hπ']; exact hker b) φ)
  exact ⟨⟨x, hxf⟩, Subtype.ext hπx⟩
end _root_.GlobalTheory
end GlobalTheory
