-- Prove2me | solution 1 for GlobalTheory.PowerSeriesNormal.dvd_of_pow_dvd_powerSeries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:04:53.380184+00:00
-- url     : https://prove2.me/submissions/a5766b0f-a379-49e2-ae0b-66944378b853

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsIntegrallyClosedPowerSeries
import Theorems.Thm_GlobalTheory_PowerSeriesNormal_exists_eq_X_pow_mul
import Theorems.Thm_GlobalTheory_PowerSeriesNormal_almostMultiples_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.PowerSeriesNormal
open PowerSeries
variable {R : Type} [CommRing R] [IsDomain R]
namespace GlobalTheory.PowerSeriesNormal
theorem _root_.solution [IsNoetherianRing R] [IsIntegrallyClosed R] {f g h : R⟦X⟧}
    (hg : g ≠ 0) (hh : h ≠ 0) (H : ∀ n : ℕ, g ^ n ∣ h * f ^ n) : g ∣ f := by
  obtain ⟨a, g₁, hg₁, rfl⟩ := exists_eq_X_pow_mul hg
  have hg₁0 : g₁ ≠ 0 := by rintro rfl; exact hg₁ (dvd_zero _)
  have hmem : f ∈ almostMultiples g₁ := ⟨h, hh, fun n =>
    (pow_dvd_pow_of_dvd (dvd_mul_left g₁ (X ^ a)) n).trans (H n)⟩
  obtain ⟨f', rfl⟩ := Ideal.mem_span_singleton.1 (almostMultiples_le hg₁ hmem)
  rcases eq_or_ne f' 0 with rfl | hf'
  · simp
  obtain ⟨e, f₁, hf₁, rfl⟩ := exists_eq_X_pow_mul hf'
  obtain ⟨b, h₁, hh₁, rfl⟩ := exists_eq_X_pow_mul hh
  have h1 : g₁ ^ (b + 1) * X ^ (a * (b + 1)) ∣
      g₁ ^ (b + 1) * (X ^ (b + e * (b + 1)) * (h₁ * f₁ ^ (b + 1))) := by
    have e1 : (X ^ a * g₁) ^ (b + 1) = g₁ ^ (b + 1) * X ^ (a * (b + 1)) := by ring
    have e2 : X ^ b * h₁ * (g₁ * (X ^ e * f₁)) ^ (b + 1) =
        g₁ ^ (b + 1) * (X ^ (b + e * (b + 1)) * (h₁ * f₁ ^ (b + 1))) := by ring
    rw [← e1, ← e2]; exact H (b + 1)
  have h2 := (mul_dvd_mul_iff_left (pow_ne_zero (b + 1) hg₁0)).1 h1
  have hw : ¬ (X : R⟦X⟧) ∣ h₁ * f₁ ^ (b + 1) := fun hX =>
    (X_prime.dvd_or_dvd hX).elim hh₁ fun h' => hf₁ (X_prime.dvd_of_dvd_pow h')
  have hae : a ≤ e := by
    by_contra hlt
    push Not at hlt
    have h3 : (X : R⟦X⟧) ^ (b + e * (b + 1) + 1) ∣ X ^ (b + e * (b + 1)) * (h₁ * f₁ ^ (b + 1)) :=
      (pow_dvd_pow X (by nlinarith)).trans h2
    rw [pow_succ] at h3
    exact hw ((mul_dvd_mul_iff_left (pow_ne_zero _ (X_ne_zero (R := R)))).1 h3)
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hae
  exact ⟨X ^ d * f₁, by ring⟩
end GlobalTheory.PowerSeriesNormal
