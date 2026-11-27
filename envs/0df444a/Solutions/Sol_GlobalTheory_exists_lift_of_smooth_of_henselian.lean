-- Prove2me | solution 1 for GlobalTheory.exists_lift_of_smooth_of_henselian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:37:58.753815+00:00
-- url     : https://prove2.me/submissions/a4f341a0-db5f-4692-bd59-8a6b955f5b75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsCompletionPointClosedPointMemOfSmooth
import Theorems.Thm_GlobalTheory_range_subset_opens_of_isLocalRing
import Theorems.Thm_GlobalTheory_exists_isAffineOpen_pair
import Theorems.Thm_GlobalTheory_exists_lift_of_smooth_of_isAffineOpen
import Theorems.Thm_GlobalTheory_exists_algHom_lift_of_smooth
import Theorems.Thm_GlobalTheory_isLocalRing_of_surjective_of_henselian
import Theorems.Thm_GlobalTheory_isUnit_of_isUnit_map_of_henselian


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
namespace GlobalTheory
theorem _root_.solution [Smooth f] {B C : CommRingCat.{u}} [IsLocalRing B]
    (π : B ⟶ C) (hπ : Function.Surjective π) [HenselianRing B (RingHom.ker π.hom)]
    (s : Spec B ⟶ S) (x₀ : Spec C ⟶ X) (h : x₀ ≫ f = Spec.map π ≫ s) :
    ∃ x : Spec B ⟶ X, Spec.map π ≫ x = x₀ ∧ x ≫ f = s := by
  have : IsLocalRing C :=
    isLocalRing_of_surjective_of_henselian (RingHom.ker π.hom) π.hom hπ fun _ => Iff.rfl
  have : IsLocalHom π.hom := ⟨fun b hb =>
    isUnit_of_isUnit_map_of_henselian (RingHom.ker π.hom) π.hom hπ (fun _ => Iff.rfl) hb⟩
  obtain ⟨U, V, hU, hV, hVU, -, hxV⟩ :=
    exists_isAffineOpen_pair f (x₀ (closedPoint C)) (O := ⊤) trivial
  refine exists_lift_of_smooth_of_isAffineOpen f hU hV hVU π s x₀ h
    (range_subset_opens_of_isLocalRing s ?_) (range_subset_opens_of_isLocalRing x₀ hxV) ?_
  · have e : f (x₀ (closedPoint C)) = s (Spec.map π (closedPoint C)) :=
      congr($h (closedPoint C))
    rw [← Spec_closedPoint (f := π), ← e]
    exact hVU hxV
  · intro R A _ _ _ _ _ _ π' hπ' φ
    exact exists_algHom_lift_of_smooth (RingHom.ker π.hom) π'
      (fun c => (hπ c).imp fun b hb => (hπ' b).trans hb) (fun b => by rw [hπ']; rfl) φ
end GlobalTheory
