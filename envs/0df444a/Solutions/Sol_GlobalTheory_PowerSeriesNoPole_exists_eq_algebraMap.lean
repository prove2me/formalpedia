-- Prove2me | solution 1 for GlobalTheory.PowerSeriesNoPole.exists_eq_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:05:30.851645+00:00
-- url     : https://prove2.me/submissions/1835db9f-c272-4922-9b4b-5e0f64781b0b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPowerSeriesOfNoPoleAwayUniformizerX
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open scoped LaurentSeries
namespace GlobalTheory.PowerSeriesNoPole
open scoped LaurentSeries in
open PowerSeries in
private lemma C_dvd_iff_map_mk_eq_zero {A : Type} [CommRing A] (ϖ : A) (f : PowerSeries A) :
    C ϖ ∣ f ↔ PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) f = 0 := by
  constructor
  · rintro ⟨q, rfl⟩
    ext d
    simp [coeff_C_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  · intro h
    have hd : ∀ d, ϖ ∣ coeff d f := fun d ↦ by
      have := congrArg (coeff d) h
      simpa [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] using this
    choose q hq using hd
    refine ⟨mk q, ?_⟩
    ext d
    simp [coeff_C_mul, hq d]
open scoped LaurentSeries in
open PowerSeries in
private lemma prime_C_powerSeries {A : Type} [CommRing A] [IsDomain A] {ϖ : A} (hϖ : Prime ϖ) :
    Prime (C ϖ : PowerSeries A) := by
  haveI : (Ideal.span {ϖ}).IsPrime := (Ideal.span_singleton_prime hϖ.ne_zero).2 hϖ
  refine ⟨fun h ↦ hϖ.ne_zero (by simpa using congrArg (coeff 0) h), fun hu ↦ hϖ.not_unit ?_,
    fun f g h ↦ ?_⟩
  · simpa using hu.map (constantCoeff (R := A))
  · rw [C_dvd_iff_map_mk_eq_zero, C_dvd_iff_map_mk_eq_zero]
    rw [C_dvd_iff_map_mk_eq_zero, map_mul] at h
    exact mul_eq_zero.mp h
end GlobalTheory.PowerSeriesNoPole
end

set_option autoImplicit false
open scoped LaurentSeries
open GlobalTheory GlobalTheory.PowerSeriesNoPole
open scoped LaurentSeries
open PowerSeries
namespace GlobalTheory.PowerSeriesNoPole
namespace _root_.GlobalTheory.PowerSeriesNoPole
theorem _root_.solution (A : Type) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A]
    (ϖ : A) (hϖ : Irreducible ϖ) (k : A →+* ℂ) (hk : Function.Injective k)
    (S : Type) [CommRing S] [Algebra (PowerSeries A) S]
    [IsLocalization.Away (PowerSeries.C ϖ * PowerSeries.X : PowerSeries A) S]
    (ι : S →+* ℂ⸨X⸩)
    (hι : ∀ s : PowerSeries A,
      ι (algebraMap _ S s) = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.map k s))
    (v : S) (hv : ι v ∈ (HahnSeries.ofPowerSeries ℤ ℂ).range)
    (hst : ∃ s t : PowerSeries A, ¬ PowerSeries.C ϖ ∣ t ∧
      v * algebraMap _ S t = algebraMap _ S s) :
    ∃ s : PowerSeries A, v = algebraMap _ S s := by
  obtain ⟨s, t, ht, hvt⟩ := hst
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj (C ϖ * X : PowerSeries A) v
  rw [← map_pow] at ha
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have hu0 : (C ϖ * X : PowerSeries A) ≠ 0 :=
    mul_ne_zero (fun h ↦ hϖ0 (by simpa using congrArg (coeff 0) h)) X_ne_zero
  have hinj : Function.Injective (algebraMap (PowerSeries A) S) :=
    IsLocalization.injective S (powers_le_nonZeroDivisors_of_noZeroDivisors hu0)
  have hat : a * t = s * (C ϖ * X) ^ n := by
    apply hinj
    rw [map_mul, map_mul, ← ha, ← hvt]
    ring
  obtain ⟨g, hg⟩ := hv
  have hga : g * PowerSeries.map k ((C ϖ * X) ^ n) = PowerSeries.map k a := by
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
    rw [map_mul, hg, ← hι, ← hι, ← map_mul, ha]
  have hXa : (X : PowerSeries A) ^ n ∣ a := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro d hd
    apply hk
    rw [map_zero, ← PowerSeries.coeff_map, ← hga]
    have hdvd : (X : PowerSeries ℂ) ^ n ∣ g * PowerSeries.map k ((C ϖ * X) ^ n) :=
      ⟨g * C (k ϖ) ^ n, by rw [map_pow, map_mul, map_C, map_X, mul_pow]; ring⟩
    exact (PowerSeries.X_pow_dvd_iff.mp hdvd) d hd
  obtain ⟨a₁, rfl⟩ := hXa
  have ha₁ : a₁ * t = (C ϖ) ^ n * s := by
    have hX : (X : PowerSeries A) ^ n ≠ 0 := pow_ne_zero _ X_ne_zero
    apply mul_left_cancel₀ hX
    rw [mul_pow] at hat
    linear_combination hat
  have hp : Prime (C ϖ : PowerSeries A) := prime_C_powerSeries hϖ.prime
  obtain ⟨a₂, rfl⟩ := hp.pow_dvd_of_dvd_mul_right n ht ⟨s, ha₁⟩
  refine ⟨a₂, ?_⟩
  have hunit : IsUnit (algebraMap (PowerSeries A) S ((C ϖ * X) ^ n)) :=
    IsLocalization.map_units S (⟨(C ϖ * X) ^ n, n, rfl⟩ : Submonoid.powers (C ϖ * X))
  apply hunit.mul_left_inj.mp
  rw [ha, ← map_mul]
  congr 1
  ring
end _root_.GlobalTheory.PowerSeriesNoPole
end GlobalTheory.PowerSeriesNoPole
