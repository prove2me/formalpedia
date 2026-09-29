-- Prove2me | solution 1 for ModularCurve.exists_laurentSeries_int_modularUnitSeries_coeffMap_eq_jqModC_pow_of_lt_five
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/483d67d0-06fc-5137-9a2b-1b2c1d24d48d

import Mathlib
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_ModularCurve_pow_char_eq_qExpand_of_coeff_fixed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_laurentSeries_int_modularUnitSeries_coeffMap_eq_jqModC_pow_of_lt_five

set_option autoImplicit false

open ModularCurve

universe u

namespace OggSmallQ

noncomputable section

private def deltaZ : LaurentSeries ℤ :=
  HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnit

private def deltaInvZ : LaurentSeries ℤ :=
  HahnSeries.single (-1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnitInv

private theorem deltaZ_mul_deltaInvZ : deltaZ * deltaInvZ = 1 := by
  have hs : HahnSeries.single (1 : ℤ) (1 : ℤ) * HahnSeries.single (-1 : ℤ) (1 : ℤ) = 1 := by
    rw [HahnSeries.single_mul_single]
    simp
  have ho : HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnit
      * HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnitInv = 1 := by
    rw [← RingHom.map_mul, dedekindEtaUnit_mul_inv, RingHom.map_one]
  rw [deltaZ, deltaInvZ, mul_mul_mul_comm, hs, ho, one_mul]

private def xInt (p : ℕ) [NeZero p] : LaurentSeries ℤ :=
  deltaZ * qExpand ℤ p deltaInvZ

private theorem coeffMap_qExpand {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (N : ℕ) [NeZero N] (y : LaurentSeries R) :
    coeffMap f (qExpand R N y) = qExpand S N (coeffMap f y) := by
  ext k
  by_cases hk : (N : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd N _ hk, qExpand_coeff_of_not_dvd N _ hk,
      map_zero]

private theorem coeffMap_ofPowerSeries {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (w : PowerSeries R) :
    coeffMap f (HahnSeries.ofPowerSeries ℤ R w) = HahnSeries.ofPowerSeries ℤ S (w.map f) := by
  ext k
  rw [coeffMap_coeff]
  rcases le_or_gt 0 k with hk | hk
  · lift k to ℕ using hk
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff,
      PowerSeries.coeff_map]
  · rw [ofPowerSeries_coeff_of_neg _ hk, ofPowerSeries_coeff_of_neg _ hk, map_zero]

private theorem coeffMap_deltaZ {K : Type*} [CommRing K] :
    coeffMap (Int.castRingHom K) deltaZ
      = HahnSeries.single (1 : ℤ) 1
          * HahnSeries.ofPowerSeries ℤ K (dedekindEtaUnit.map (Int.castRingHom K)) := by
  rw [deltaZ, map_mul, coeffMap_single, map_one, coeffMap_ofPowerSeries]

private theorem coeffMap_deltaInvZ {K : Type*} [CommRing K] :
    coeffMap (Int.castRingHom K) deltaInvZ
      = HahnSeries.single (-1 : ℤ) 1
          * HahnSeries.ofPowerSeries ℤ K (dedekindEtaUnitInv.map (Int.castRingHom K)) := by
  rw [deltaInvZ, map_mul, coeffMap_single, map_one, coeffMap_ofPowerSeries]

private theorem coeffMap_coeff_pow_char {K : Type*} [CommRing K] (p : ℕ) [Fact p.Prime]
    [CharP K p] (y : LaurentSeries ℤ) (k : ℤ) :
    (coeffMap (Int.castRingHom K) y).coeff k ^ p = (coeffMap (Int.castRingHom K) y).coeff k := by
  rw [coeffMap_coeff]
  have h : Int.castRingHom K = (ZMod.castHom (dvd_refl p) K).comp (Int.castRingHom (ZMod p)) :=
    RingHom.ext_int _ _
  rw [h, RingHom.comp_apply, ← map_pow, ZMod.pow_card]

private theorem coeffMap_xInt_rat (p : ℕ) [NeZero p] :
    coeffMap (Int.castRingHom ℚ) (xInt p) = modularUnitSeries p := by
  have hΔ : coeffMap (Int.castRingHom ℚ) deltaZ = deltaSeries := by
    rw [coeffMap_deltaZ]; rfl
  have hone : qExpand ℚ p (coeffMap (Int.castRingHom ℚ) deltaInvZ) * deltaSeriesN p = 1 := by
    rw [deltaSeriesN, ← hΔ, ← map_mul, ← map_mul, mul_comm, deltaZ_mul_deltaInvZ, map_one,
      map_one]
  rw [xInt, map_mul, coeffMap_qExpand, hΔ, modularUnitSeries]
  congr 1
  exact eq_inv_of_mul_eq_one_left hone

private theorem eisenstein4_map_eq_one (K : Type*) [CommRing K] (p : ℕ) [CharP K p]
    (h : p ∣ 240) : eisenstein4.map (Int.castRingHom K) = 1 := by
  have h240 : (240 : K) = 0 := by
    have := (CharP.cast_eq_zero_iff K p 240).2 h
    simpa using this
  ext n
  rw [PowerSeries.coeff_map]
  simp only [eisenstein4, PowerSeries.coeff_mk, PowerSeries.coeff_one]
  split_ifs
  · simp
  · simp [h240]

private theorem jqModC_eq_coeffMap_deltaInvZ (K : Type*) [CommRing K] (p : ℕ) [CharP K p]
    (h : p ∣ 240) : jqModC K = coeffMap (Int.castRingHom K) deltaInvZ := by
  rw [coeffMap_deltaInvZ, jqModC, jNum, map_mul, map_pow, eisenstein4_map_eq_one K p h,
    one_pow, one_mul]

private theorem coeffMap_xInt_charP (p : ℕ) [Fact p.Prime] (h : p ∣ 240)
    (κ : Type u) [Field κ] [CharP κ p] :
    coeffMap (Int.castRingHom κ) (xInt p) = jqModC κ ^ (p - 1) := by
  have hprime : p.Prime := Fact.out
  have hj := jqModC_eq_coeffMap_deltaInvZ κ p h

  have hfrob : qExpand κ p (jqModC κ) = jqModC κ ^ p := by
    rw [hj]
    exact (pow_char_eq_qExpand_of_coeff_fixed p _ (coeffMap_coeff_pow_char p deltaInvZ)).symm

  have hone : coeffMap (Int.castRingHom κ) deltaZ * jqModC κ = 1 := by
    rw [hj, ← map_mul, deltaZ_mul_deltaInvZ, map_one]
  have hpow : jqModC κ ^ p = jqModC κ * jqModC κ ^ (p - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hprime.one_le]
  rw [xInt, map_mul, coeffMap_qExpand, ← hj, hfrob, hpow, ← mul_assoc, hone, one_mul]

end

end OggSmallQ

theorem solution
    (p : ℕ) [Fact p.Prime] (hp : p < 5) :
    ∃ x : LaurentSeries ℤ, coeffMap (Int.castRingHom ℚ) x = modularUnitSeries p ∧
      ∀ (κ : Type u) [Field κ] [CharP κ p],
        coeffMap (Int.castRingHom κ) x = jqModC κ ^ (p - 1) := by
  have hprime : p.Prime := Fact.out
  have h240 : p ∣ 240 := by
    interval_cases p <;> first | decide | exact absurd hprime (by decide)
  exact ⟨OggSmallQ.xInt p, OggSmallQ.coeffMap_xInt_rat p,
    fun κ _ _ => OggSmallQ.coeffMap_xInt_charP p h240 κ⟩

#print axioms solution

end S_ModularCurve_exists_laurentSeries_int_modularUnitSeries_coeffMap_eq_jqModC_pow_of_lt_five
end P2MW
export P2MW.S_ModularCurve_exists_laurentSeries_int_modularUnitSeries_coeffMap_eq_jqModC_pow_of_lt_five (solution)
