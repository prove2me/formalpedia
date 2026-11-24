-- Prove2me | solution 1 for GlobalTheory.awayMap_bijective_of_range_eq_subalgebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:23:21.016041+00:00
-- url     : https://prove2.me/submissions/061105da-f9a5-4236-8507-852c7e019eca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AwayMapBijectiveOfRangeEqSubalgebra

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits Scheme.AffineZariskiSite
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (R A B : Type) [CommRing R] [CommRing A] [CommRing B] [Algebra R B] (C : Subalgebra R B) (φ : A →+* B), Function.Injective φ → ∀ (_ : ∀ x, x ∈ C ↔ ∃ y, φ y = x) (a : A) (b : B), φ a = b → (∀ hb : b ∈ C, Function.Bijective (Localization.awayMap C.val.toRingHom (⟨b, hb⟩ : C))) → Function.Bijective (Localization.awayMap φ a) := by
  intro R A B _ _ _ _ C φ hφ hC a b hab hloc
  subst hab
  have hmem : ∀ y, φ y ∈ C := fun y => (hC _).2 ⟨y, rfl⟩
  let f : A →+* C := φ.codRestrict C.toSubsemiring hmem
  have hf : Function.Bijective f := by
    refine ⟨fun x y h => hφ (congrArg Subtype.val h), fun c => ?_⟩
    obtain ⟨y, hy⟩ := (hC c.1).1 c.2
    exact ⟨y, Subtype.ext hy⟩
  let e : A ≃+* C := RingEquiv.ofBijective f hf
  have H : Submonoid.map e.toMonoidHom (Submonoid.powers a) = Submonoid.powers (f a) :=
    Submonoid.map_powers e.toMonoidHom a
  have h1 : Function.Bijective (Localization.awayMap f a) := by
    have hb := (IsLocalization.ringEquivOfRingEquiv (Localization.Away a)
      (Localization.Away (f a)) e H).bijective
    have key : ∀ z, Localization.awayMap f a z =
        IsLocalization.ringEquivOfRingEquiv (Localization.Away a) (Localization.Away (f a)) e H z := by
      intro z
      rw [IsLocalization.ringEquivOfRingEquiv_apply]
      rfl
    rw [show (Localization.awayMap f a : Localization.Away a → Localization.Away (f a)) = _ from funext key]
    exact hb
  have h2 : Localization.awayMap φ a =
      (Localization.awayMap C.val.toRingHom (f a)).comp (Localization.awayMap f a) := by
    simp only [Localization.awayMap, IsLocalization.Away.map]
    rw [IsLocalization.map_comp_map]
    rfl
  rw [h2]
  exact (hloc (hmem a)).comp h1
end GlobalTheory
