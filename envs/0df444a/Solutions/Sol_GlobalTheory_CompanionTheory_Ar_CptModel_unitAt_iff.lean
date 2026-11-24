-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.CptModel.unitAt_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:17:20.397329+00:00
-- url     : https://prove2.me/submissions/963dbeec-c98d-4874-837b-053d1e2aa1b6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsCptGen
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InjectiveOfIsCptGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.CptModel
open AlgebraicGeometry CategoryTheory
variable {X : Scheme.{0}} {Ω : Type} [Field Ω]
namespace GlobalTheory.CompanionTheory.Ar.CptModel
theorem _root_.solution (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) (a : Ω) :
    unitAt ξ p a ↔ ∃ s : X.presheaf.stalk p.1, IsUnit s ∧ genMap ξ p s = a := by
  constructor
  · rintro ⟨h0, ⟨s, hs⟩, ⟨t, ht⟩⟩
    refine ⟨s, ?_, hs⟩
    have h1 : genMap ξ p (1 - s * t) = 0 := by
      rw [map_sub, map_mul, map_one, hs, ht, mul_inv_cancel₀ h0, sub_self]
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (s * t) with h | h
    · exact isUnit_of_mul_isUnit_left h
    · exact absurd (h1 ▸ h.map (genMap ξ p)) not_isUnit_zero
  · rintro ⟨s, ⟨u, rfl⟩, rfl⟩
    refine ⟨(u.isUnit.map (genMap ξ p)).ne_zero, ⟨_, rfl⟩, ⟨(u⁻¹ : _ˣ), ?_⟩⟩
    exact (map_units_inv (genMap ξ p) u)
end GlobalTheory.CompanionTheory.Ar.CptModel
