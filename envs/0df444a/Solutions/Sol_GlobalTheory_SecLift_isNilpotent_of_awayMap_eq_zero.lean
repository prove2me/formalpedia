-- Prove2me | solution 1 for GlobalTheory.SecLift.isNilpotent_of_awayMap_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:37:19.092046+00:00
-- url     : https://prove2.me/submissions/d7eeae5a-7526-478c-bc59-95f73ff88f5d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LiftAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsCompletionPointClosedPointMemOfSmooth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_FiniteLocalLifts_SmLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSmoothSectionLiftBasicOpenAffine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SecLift
variable {R R₀ : Type} [CommRing R] [CommRing R₀]
namespace GlobalTheory.SecLift
theorem _root_.solution (π : R →+* R₀) (hnil : IsNilpotent (RingHom.ker π)) (f : R)
    (x : Localization.Away f) (hx : Localization.awayMap π f x = 0) : IsNilpotent x := by
  obtain ⟨N, hN⟩ := hnil
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers f) x
  have hc : (Localization.awayMap π f).comp (algebraMap R (Localization.Away f)) =
      (algebraMap R₀ (Localization.Away (π f))).comp π := IsLocalization.map_comp _
  have h1 : algebraMap R₀ (Localization.Away (π f)) (π a) = 0 := by
    have := congrArg (Localization.awayMap π f) hs
    rw [map_mul, hx, zero_mul] at this
    rw [← RingHom.comp_apply, ← hc, RingHom.comp_apply, ← this]
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (π f)) _ _).1 h1
  have hmem : f ^ k * a ∈ RingHom.ker π := by
    rw [RingHom.mem_ker, map_mul, map_pow]; exact hk
  have h0 : (f ^ k * a) ^ N = 0 := by
    have := Ideal.pow_mem_pow hmem N
    rw [hN] at this
    exact Ideal.mem_bot.1 this
  have hu : IsUnit (algebraMap R (Localization.Away f) (s * f ^ k)) := by
    rw [map_mul, map_pow]
    exact (IsLocalization.map_units _ s).mul ((IsLocalization.Away.algebraMap_isUnit f).pow k)
  refine ⟨N, (hu.pow N).mul_left_eq_zero.1 ?_⟩
  rw [← mul_pow, map_mul, ← mul_assoc, hs, ← map_mul, mul_comm a, ← map_pow, h0, map_zero]
end GlobalTheory.SecLift
