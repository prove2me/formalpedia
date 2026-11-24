-- Prove2me | solution 1 for GlobalTheory.AwaySubalgebraEmbedding.exists_away_subalgebra_embedding
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:58:56.863886+00:00
-- url     : https://prove2.me/submissions/13b6610f-e485-4e1e-b7b5-0525c11d9796

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsAwaySubalgebraEmbedding

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AwaySubalgebraEmbedding
namespace GlobalTheory.AwaySubalgebraEmbedding
theorem _root_.solution (K : Type) [Field K] (S : Type) [CommRing S]
    [Algebra K S] (S₁ : Subalgebra K S) (x : S) (hx : x ∈ S₁) :
    ∃ (κ : Localization.Away (⟨x, hx⟩ : S₁) →ₐ[K] Localization.Away x),
      (∀ s : S₁, κ (algebraMap S₁ (Localization.Away (⟨x, hx⟩ : S₁)) s)
        = algebraMap S (Localization.Away x) (s : S)) ∧
      Function.Injective κ ∧
      ∀ (z : Localization.Away x) (m : ℕ), ∀ s ∈ S₁,
        z * algebraMap S (Localization.Away x) x ^ m = algebraMap S (Localization.Away x) s →
          z ∈ AlgHom.range κ := by
  let f : S₁ →ₐ[K] Localization.Away x :=
    (IsScalarTower.toAlgHom K S (Localization.Away x)).comp S₁.val
  have hxu : IsUnit (algebraMap S (Localization.Away x) x) :=
    IsLocalization.Away.algebraMap_isUnit x
  have hf : ∀ y : Submonoid.powers (⟨x, hx⟩ : S₁), IsUnit (f y) := by
    rintro ⟨y, n, rfl⟩
    simp only [map_pow]
    exact hxu.pow n
  let κ : Localization.Away (⟨x, hx⟩ : S₁) →ₐ[K] Localization.Away x :=
    IsLocalization.liftAlgHom (M := Submonoid.powers (⟨x, hx⟩ : S₁)) hf
  have hκ : ∀ s : S₁, κ (algebraMap S₁ (Localization.Away (⟨x, hx⟩ : S₁)) s)
      = algebraMap S (Localization.Away x) (s : S) := by
    intro s
    exact IsLocalization.lift_eq (M := Submonoid.powers (⟨x, hx⟩ : S₁))
      (g := (f : S₁ →+* Localization.Away x)) hf s
  have hxu₁ : IsUnit (algebraMap S₁ (Localization.Away (⟨x, hx⟩ : S₁)) ⟨x, hx⟩) :=
    IsLocalization.Away.algebraMap_isUnit _
  refine ⟨κ, hκ, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨n, s, hs⟩ := IsLocalization.Away.surj (⟨x, hx⟩ : S₁) a
    have h0 : algebraMap S (Localization.Away x) (s : S) = 0 := by
      rw [← hκ, ← hs, map_mul, ha, zero_mul]
    obtain ⟨⟨_, k, rfl⟩, hk⟩ :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers x) (Localization.Away x) _).1 h0
    have h1 : (⟨x, hx⟩ : S₁) ^ k * s = 0 := by
      apply Subtype.ext
      simpa using hk
    have h2 : a * algebraMap S₁ (Localization.Away (⟨x, hx⟩ : S₁)) ⟨x, hx⟩ ^ (n + k) = 0 := by
      rw [pow_add, ← mul_assoc, hs, ← map_pow, ← map_mul, mul_comm, h1, map_zero]
    exact (hxu₁.pow (n + k)).mul_left_eq_zero.1 h2
  · intro z m s hs hz
    obtain ⟨u, hu⟩ := hxu₁.pow m
    refine ⟨algebraMap S₁ (Localization.Away (⟨x, hx⟩ : S₁)) ⟨s, hs⟩ * ↑u⁻¹, ?_⟩
    apply (hxu.pow m).mul_right_cancel
    have h3 : κ ↑u = algebraMap S (Localization.Away x) x ^ m := by
      rw [hu, map_pow, hκ]
    show κ _ * _ = _
    rw [hz, ← h3, ← map_mul, mul_assoc, Units.inv_mul, mul_one, hκ]
end GlobalTheory.AwaySubalgebraEmbedding
