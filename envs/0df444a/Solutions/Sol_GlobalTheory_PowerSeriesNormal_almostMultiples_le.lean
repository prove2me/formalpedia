-- Prove2me | solution 1 for GlobalTheory.PowerSeriesNormal.almostMultiples_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:46:34.715053+00:00
-- url     : https://prove2.me/submissions/c584d2b7-8eed-4087-bc40-60fb80336276

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsIntegrallyClosedPowerSeries
import Theorems.Thm_GlobalTheory_PowerSeriesNormal_dvd_of_pow_dvd
import Theorems.Thm_GlobalTheory_PowerSeriesNormal_dvd_of_dvd_X_pow_mul
import Theorems.Thm_GlobalTheory_PowerSeriesNormal_exists_eq_X_pow_mul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open IsLocalRing
namespace GlobalTheory.PowerSeriesNormal
open PowerSeries
variable {R : Type} [CommRing R] [IsDomain R]
private theorem mem_almostMultiples_iff {g f : R⟦X⟧} :
    f ∈ almostMultiples g ↔ ∃ h, h ≠ 0 ∧ ∀ n : ℕ, g ^ n ∣ h * f ^ n := Iff.rfl
private theorem constantCoeff_dvd_of_mem_almostMultiples [IsNoetherianRing R] [IsIntegrallyClosed R] {g e : R⟦X⟧}
    (hg : ¬ (X : R⟦X⟧) ∣ g) (he : e ∈ almostMultiples g) :
    constantCoeff g ∣ constantCoeff e := by
  obtain ⟨h, hh, H⟩ := mem_almostMultiples_iff.1 he
  obtain ⟨b, h₁, hh₁, rfl⟩ := exists_eq_X_pow_mul hh
  have H' : ∀ n : ℕ, g ^ n ∣ h₁ * e ^ n := fun n =>
    dvd_of_dvd_X_pow_mul (fun hX => hg (X_prime.dvd_of_dvd_pow hX))
      (c := b) (by simpa [mul_assoc] using H n)
  have hg0 : constantCoeff g ≠ 0 := fun h0 => hg (X_dvd_iff.2 h0)
  have hh0 : constantCoeff h₁ ≠ 0 := fun h0 => hh₁ (X_dvd_iff.2 h0)
  exact dvd_of_pow_dvd hg0 hh0 fun n => by
    simpa [map_mul, map_pow] using map_dvd constantCoeff (H' n)
private theorem mem_almostMultiples_of_X_pow_mul_mem {g e : R⟦X⟧} (hg : ¬ (X : R⟦X⟧) ∣ g) {k : ℕ}
    (he : X ^ k * e ∈ almostMultiples g) : e ∈ almostMultiples g := by
  obtain ⟨h, hh, H⟩ := mem_almostMultiples_iff.1 he
  refine mem_almostMultiples_iff.2 ⟨h, hh, fun n => ?_⟩
  have : h * (X ^ k * e) ^ n = X ^ (k * n) * (h * e ^ n) := by ring
  exact dvd_of_dvd_X_pow_mul (fun hX => hg (X_prime.dvd_of_dvd_pow hX)) (this ▸ H n)
private theorem exists_X_pow_dvd_sub_mul_of_mem_almostMultiples [IsNoetherianRing R] [IsIntegrallyClosed R] {g f : R⟦X⟧}
    (hg : ¬ (X : R⟦X⟧) ∣ g) (hf : f ∈ almostMultiples g) :
    ∀ k : ℕ, ∃ r : R⟦X⟧, X ^ k ∣ f - g * r := by
  have hgI : g ∈ almostMultiples g :=
    mem_almostMultiples_iff.2 ⟨1, one_ne_zero, fun n => by rw [one_mul]⟩
  intro k
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨r, e, he⟩ := ih
    have hmem : X ^ k * e ∈ almostMultiples g := by
      rw [← he]; exact Ideal.sub_mem _ hf (Ideal.mul_mem_right _ _ hgI)
    obtain ⟨c, hc⟩ := constantCoeff_dvd_of_mem_almostMultiples hg (mem_almostMultiples_of_X_pow_mul_mem hg hmem)
    refine ⟨r + C c * X ^ k, ?_⟩
    have hX : (X : R⟦X⟧) ∣ e - g * C c := by
      rw [X_dvd_iff]; simp [hc]
    obtain ⟨w, hw⟩ := hX
    refine ⟨w, ?_⟩
    have : f - g * (r + C c * X ^ k) = X ^ k * (e - g * C c) := by
      linear_combination he
    rw [this, hw]; ring
end GlobalTheory.PowerSeriesNormal
end

set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.PowerSeriesNormal
open PowerSeries
variable {R : Type} [CommRing R] [IsDomain R]
namespace GlobalTheory.PowerSeriesNormal
theorem _root_.solution [IsNoetherianRing R] [IsIntegrallyClosed R] {g : R⟦X⟧}
    (hg : ¬ (X : R⟦X⟧) ∣ g) : almostMultiples g ≤ Ideal.span {g} := by
  intro f hf
  rw [Ideal.mem_span_singleton]
  choose r hr using exists_X_pow_dvd_sub_mul_of_mem_almostMultiples hg hf
  have hstable : ∀ j m : ℕ, j ≤ m → coeff j (r (m + 1)) = coeff j (r (j + 1)) := by
    intro j m hjm
    have h1 : X ^ (j + 1) ∣ g * (r (j + 1) - r (m + 1)) := by
      have e1 : g * (r (j + 1) - r (m + 1)) = (f - g * r (m + 1)) - (f - g * r (j + 1)) := by ring
      rw [e1]
      exact dvd_sub ((pow_dvd_pow X (by omega)).trans (hr (m + 1))) (hr (j + 1))
    have h2 := X_prime.pow_dvd_of_dvd_mul_left (j + 1) hg h1
    rw [X_pow_dvd_iff] at h2
    have := h2 j (Nat.lt_succ_self j)
    rw [map_sub, sub_eq_zero] at this
    exact this.symm
  refine ⟨mk fun k => coeff k (r (k + 1)), ?_⟩
  rw [← sub_eq_zero]
  ext m
  rw [map_zero]
  have hq : X ^ (m + 1) ∣ r (m + 1) - mk fun k => coeff k (r (k + 1)) := by
    rw [X_pow_dvd_iff]
    intro j hj
    rw [map_sub, coeff_mk, hstable j m (by omega), sub_self]
  have hsum : X ^ (m + 1) ∣ f - g * mk fun k => coeff k (r (k + 1)) := by
    have e1 : f - g * (mk fun k => coeff k (r (k + 1))) =
        (f - g * r (m + 1)) + g * (r (m + 1) - mk fun k => coeff k (r (k + 1))) := by ring
    rw [e1]
    exact dvd_add (hr (m + 1)) (dvd_mul_of_dvd_right hq g)
  rw [X_pow_dvd_iff] at hsum
  exact hsum m (Nat.lt_succ_self m)
end GlobalTheory.PowerSeriesNormal
