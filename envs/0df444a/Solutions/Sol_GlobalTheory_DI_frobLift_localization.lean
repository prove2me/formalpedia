-- Prove2me | solution 1 for GlobalTheory.DI.frobLift_localization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:39:06.044312+00:00
-- url     : https://prove2.me/submissions/19d9f09f-8b23-4fb1-a410-205f9b2a7b98

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FrobLiftLocalization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
open GlobalTheory GlobalTheory.DI
namespace GlobalTheory.DI
theorem _root_.solution :
    ∀ (p : ℕ) [Fact p.Prime] {B Kt : Type} [CommRing B] [CommRing Kt] [Algebra B Kt]
      (S : Submonoid B) [IsLocalization S Kt] (F : B →+* B), (p : B) ^ 2 = 0 →
      (∀ z, ∃ w, F z = z ^ p + p * w) →
      ∃ F' : Kt →+* Kt, (∀ b, F' (algebraMap B Kt b) = algebraMap B Kt (F b)) ∧
        ∀ z, ∃ w, F' z = z ^ p + p * w := by
  intro p _ B Kt _ _ _ S _ F hp2 hF
  have hunit : ∀ s : S, IsUnit ((algebraMap B Kt).comp F s) := by
    intro s
    obtain ⟨w, hw⟩ := hF (s : B)
    have hu : IsUnit (algebraMap B Kt (s : B) ^ p) :=
      (IsLocalization.map_units Kt s).pow p
    have hn : IsNilpotent ((p : Kt) * algebraMap B Kt w) := by
      refine ⟨2, ?_⟩
      have : (p : Kt) ^ 2 = 0 := by
        have := congrArg (algebraMap B Kt) hp2
        simpa using this
      rw [mul_pow, this, zero_mul]
    have := hn.isUnit_add_right_of_commute hu (Commute.all _ _)
    rw [add_comm] at this
    simpa [RingHom.comp_apply, hw, map_add, map_mul, map_pow, map_natCast] using this
  refine ⟨IsLocalization.lift hunit, fun b => by simp [IsLocalization.lift_eq], ?_⟩
  intro z
  obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective S z
  set z := IsLocalization.mk' Kt b s with hz
  set F' : Kt →+* Kt := IsLocalization.lift hunit
  have hF' : ∀ c, F' (algebraMap B Kt c) = algebraMap B Kt (F c) := fun c => by
    simp [F', IsLocalization.lift_eq]
  have hspec : z * algebraMap B Kt (s : B) = algebraMap B Kt b := IsLocalization.mk'_spec Kt b s
  obtain ⟨v, hv⟩ := hF b
  obtain ⟨u, hu⟩ := hF (s : B)
  have key : F' z * (algebraMap B Kt (s : B) ^ p + p * algebraMap B Kt u) =
      algebraMap B Kt b ^ p + p * algebraMap B Kt v := by
    have := congrArg F' hspec
    rw [map_mul, hF', hF', hu, hv] at this
    simpa [map_add, map_mul, map_pow, map_natCast] using this
  obtain ⟨t, ht⟩ := (IsLocalization.map_units Kt s).pow p
  refine ⟨(algebraMap B Kt v - F' z * algebraMap B Kt u) * ↑t⁻¹, ?_⟩
  have hzs : z ^ p * algebraMap B Kt (s : B) ^ p = algebraMap B Kt b ^ p := by
    rw [← mul_pow, hspec]
  have h1 : (F' z - z ^ p) * (t : Kt) = p * (algebraMap B Kt v - F' z * algebraMap B Kt u) := by
    rw [ht]; linear_combination key - hzs
  calc F' z = z ^ p + (F' z - z ^ p) * (t : Kt) * ↑t⁻¹ := by
        rw [mul_assoc, Units.mul_inv, mul_one]; ring
    _ = _ := by rw [h1]; ring
end GlobalTheory.DI
