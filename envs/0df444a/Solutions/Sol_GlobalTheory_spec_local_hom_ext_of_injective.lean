-- Prove2me | solution 1 for GlobalTheory.spec_local_hom_ext_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:33:50.053547+00:00
-- url     : https://prove2.me/submissions/27a2a8be-5eb9-4f88-95e1-663ce2bc3e11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_SRelOneOneIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpecLocalRingHomExtOfInjectiveLocalHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory
theorem _root_.solution (R R' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
    (φ : R →+* R') (hl : IsLocalHom φ) (hi : Function.Injective φ) (Y : Scheme.{0}) (x y : Sp R ⟶ Y)
    (h : spMap φ ≫ x = spMap φ ≫ y) : x = y := by
  have hc : (spMap φ) (IsLocalRing.closedPoint R') = IsLocalRing.closedPoint R := by
    have : IsLocalHom (CommRingCat.Hom.hom (CommRingCat.ofHom φ)) := hl
    exact Spec_closedPoint (R := CommRingCat.of R) (S := CommRingCat.of R') (f := CommRingCat.ofHom φ)
  have hp : x (IsLocalRing.closedPoint R) = y (IsLocalRing.closedPoint R) := by
    rw [← hc]
    change (spMap φ ≫ x) (IsLocalRing.closedPoint R') = (spMap φ ≫ y) (IsLocalRing.closedPoint R')
    rw [h]
  obtain ⟨p, hpx⟩ : ∃ p, x (IsLocalRing.closedPoint R) = p := ⟨_, rfl⟩
  have ex : ∀ z : Sp R ⟶ Y, z (IsLocalRing.closedPoint R) = p →
      ∃ a, Spec.map a ≫ Y.fromSpecStalk p = z := by
    intro z hz
    subst hz
    exact ⟨_, Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of R) z⟩
  obtain ⟨a, rfl⟩ := ex x hpx
  obtain ⟨b, rfl⟩ := ex y (hp ▸ hpx)
  have h2 : spMap φ ≫ Spec.map a = spMap φ ≫ Spec.map b := by
    rw [← Category.assoc, ← Category.assoc] at h
    exact (cancel_mono _).1 h
  have h3 : a ≫ CommRingCat.ofHom φ = b ≫ CommRingCat.ofHom φ := by
    apply Spec.map_injective
    simpa [spMap, Spec.map_comp] using h2
  have hab : a = b := by
    ext s
    apply hi
    have := congrArg (fun g => g.hom s) h3
    simpa using this
  rw [hab]
end GlobalTheory
