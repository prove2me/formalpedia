-- Prove2me | solution 1 for ModularCurve.cuspData_map_coeffMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/7274aa3b-1d90-58fc-9517-1f36f189037f

import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Theorems.Thm_ModularCurve_coeff_slotSubst_tateUnivX
import Theorems.Thm_ModularCurve_coeff_slotSubst_tateUnivY
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_cuspData_map_coeffMap

set_option autoImplicit false

noncomputable section

open HahnSeries Polynomial

namespace ModularCurve
p2m_export "ModularCurve" "coeffMap coeffMap_coeff tateToricPoint cuspPoint cuspPoint_of_eq_zero cuspPoint_of_ne_zero cuspData tateUnivX tateUnivY slotSubst nonToricPoint ofPowerSeries_coeff_of_neg LevelPData LevelPData.ext coeff_slotSubst_tateUnivX coeff_slotSubst_tateUnivY"
namespace CuspNaturalityProof
p2m_open "ModularCurve"

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)

section RootOfUnity

variable {p : ℕ} [hpr : Fact p.Prime] (ζ : R) (hζ : ∑ i ∈ Finset.range p, ζ ^ i = 0)

omit hpr in
include hζ in
theorem pow_eq_one : ζ ^ p = 1 := by
  have h := geom_sum_mul ζ p
  rw [hζ, zero_mul] at h
  exact sub_eq_zero.mp h.symm

include hζ in

theorem sum_pow_mul_eq_zero {a : ℕ} (ha : ¬ p ∣ a) : ∑ i ∈ Finset.range p, (ζ ^ a) ^ i = 0 := by
  have hp : p.Prime := hpr.out
  have hζp := pow_eq_one ζ hζ
  have hcop : Nat.Coprime p a := (Nat.Prime.coprime_iff_not_dvd hp).mpr ha
  have h1 : ∀ i, (ζ ^ a) ^ i = ζ ^ (a * i % p) := by
    intro i
    rw [← _root_.pow_mul]
    conv_lhs => rw [← Nat.mod_add_div (a * i) p, _root_.pow_add, _root_.pow_mul, hζp, one_pow, mul_one]
  simp_rw [h1]
  rw [← hζ]
  have hinj : ∀ i j : ℕ, i < p → j < p → a * i % p = a * j % p → i = j := by
    intro i j hi' hj' hij
    have hmod : a * i ≡ a * j [MOD p] := hij
    have hij' : i ≡ j [MOD p] := Nat.ModEq.cancel_left_of_coprime hcop hmod
    rw [Nat.ModEq, Nat.mod_eq_of_lt hi', Nat.mod_eq_of_lt hj'] at hij'
    exact hij'
  have hsurj := Finset.surj_on_of_inj_on_of_card_le (s := Finset.range p) (t := Finset.range p)
    (fun i _ => a * i % p) (fun i _ => Finset.mem_range.mpr (Nat.mod_lt _ hp.pos))
    (fun i j hi hj hij => hinj i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hij) le_rfl
  refine Finset.sum_nbij (fun i => a * i % p) (fun i _ => Finset.mem_range.mpr (Nat.mod_lt _ hp.pos))
    ?_ ?_ (fun _ _ => rfl)
  · intro i hi j hj hij
    exact hinj i j (Finset.mem_range.mp (Finset.mem_coe.mp hi)) (Finset.mem_range.mp (Finset.mem_coe.mp hj)) hij
  · intro b hb
    obtain ⟨i, hi, e⟩ := hsurj b (Finset.mem_coe.mp hb)
    exact ⟨i, Finset.mem_coe.mpr hi, e.symm⟩

include hζ in

theorem one_sub_pow_mul_eq {a : ℕ} (ha : ¬ p ∣ a) :
    (1 - ζ ^ a) * ∑ i ∈ Finset.range p, ∑ m ∈ Finset.range i, (ζ ^ a) ^ m = p := by
  rw [Finset.mul_sum]
  simp_rw [mul_neg_geom_sum]
  rw [Finset.sum_sub_distrib, sum_pow_mul_eq_zero ζ hζ ha, sub_zero, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_one]

include hζ in
theorem isUnit_one_sub_pow (hp : IsUnit (p : R)) {a : ℕ} (ha : ¬ p ∣ a) : IsUnit (1 - ζ ^ a) := by
  have h := one_sub_pow_mul_eq ζ hζ ha
  rw [← h] at hp
  exact isUnit_of_mul_isUnit_left hp

end RootOfUnity

theorem ofPowerSeries_coeff_of_neg (x : PowerSeries R) {k : ℤ} (hk : k < 0) :
    (HahnSeries.ofPowerSeries ℤ R x).coeff k = 0 := by
  rw [HahnSeries.ofPowerSeries_apply]
  refine HahnSeries.embDomain_notin_range ?_
  rintro ⟨n, hn⟩
  change (n : ℤ) = k at hn
  omega

theorem coeffMap_ofPowerSeries (x : PowerSeries R) :
    coeffMap f (HahnSeries.ofPowerSeries ℤ R x) = HahnSeries.ofPowerSeries ℤ S (x.map f) := by
  ext k
  rw [coeffMap_coeff]
  rcases le_or_gt 0 k with hk | hk
  · lift k to ℕ using hk
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff,
      PowerSeries.coeff_map]
  · rw [ofPowerSeries_coeff_of_neg _ hk, ofPowerSeries_coeff_of_neg _ hk, map_zero]

theorem map_units_inv (c : Rˣ) : f ((c⁻¹ : Rˣ) : R) = (((Units.map (f : R →* S) c)⁻¹ : Sˣ) : S) :=
  (Units.coe_map_inv (f : R →* S) c).symm

theorem map_units (c : Rˣ) : f (c : R) = ((Units.map (f : R →* S) c : Sˣ) : S) := rfl

theorem map_ring_inverse_of_isUnit_or_eq_zero {x : R} (hx : IsUnit x ∨ x = 0) :
    f (Ring.inverse x) = Ring.inverse (f x) := by
  rcases hx with hx | rfl
  · obtain ⟨u, rfl⟩ := hx
    rw [Ring.inverse_unit, show f (u : R) = ((Units.map (f : R →* S) u : Sˣ) : S) from rfl, Ring.inverse_unit]
    exact (Units.coe_map_inv (f : R →* S) u).symm
  · rw [Ring.inverse_zero, map_zero, Ring.inverse_zero]

theorem tateToricPoint_map (p : ℕ) (c : Rˣ) (hc : IsUnit (1 - (c : R)) ∨ (1 - (c : R)) = 0) :
    Prod.map (coeffMap f) (coeffMap f) (tateToricPoint R p c) =
      tateToricPoint S p (Units.map (f : R →* S) c) := by
  have hinv : f (Ring.inverse (1 - (c : R))) = Ring.inverse (1 - (Units.map (f : R →* S) c : S)) := by
    rw [map_ring_inverse_of_isUnit_or_eq_zero f hc, map_sub, map_one]; rfl
  simp only [tateToricPoint, Prod.map_apply, coeffMap_ofPowerSeries, Prod.mk.injEq]
  constructor
  · congr 1
    ext m
    simp only [PowerSeries.coeff_map, PowerSeries.coeff_mk]
    split_ifs with hm hpm
    · rw [map_mul, map_pow, hinv]; rfl
    · simp only [map_sub, map_sum, map_mul, map_natCast, map_add, map_pow, map_ofNat,
        apply_ite f, map_zero, map_units_inv f c]
      rfl
    · simp only [map_sub, map_sum, map_mul, map_natCast, map_add, map_pow, map_ofNat,
        apply_ite f, map_zero, map_units_inv f c]
      rfl
  · congr 1
    ext m
    simp only [PowerSeries.coeff_map, PowerSeries.coeff_mk]
    split_ifs with hm hpm
    · rw [map_mul, map_pow, map_pow, hinv]; rfl
    · simp only [map_sub, map_sum, map_mul, map_natCast, map_add, map_pow,
        apply_ite f, map_zero, map_units_inv f c]
      rfl
    · simp only [map_sub, map_sum, map_mul, map_natCast, map_add, map_pow,
        apply_ite f, map_zero, map_units_inv f c]
      rfl

theorem slotSubst_tateUnivX_map (p : ℕ) (c : Rˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    (slotSubst R p c j tateUnivX).map f = slotSubst S p (Units.map (f : R →* S) c) j tateUnivX := by
  ext n
  rw [PowerSeries.coeff_map, coeff_slotSubst_tateUnivX p c j hj hjp, coeff_slotSubst_tateUnivX p _ j hj hjp]
  simp only [map_add, map_sum, map_mul, map_sub, map_natCast, map_pow, map_ofNat, apply_ite f, map_zero,
    map_units_inv f c]
  rfl

theorem slotSubst_tateUnivY_map (p : ℕ) (c : Rˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    (slotSubst R p c j tateUnivY).map f = slotSubst S p (Units.map (f : R →* S) c) j tateUnivY := by
  ext n
  rw [PowerSeries.coeff_map, coeff_slotSubst_tateUnivY p c j hj hjp, coeff_slotSubst_tateUnivY p _ j hj hjp]
  simp only [map_add, map_sum, map_mul, map_sub, map_natCast, map_pow, apply_ite f, map_zero,
    map_units_inv f c]
  rfl

theorem nonToricPoint_map (p : ℕ) (c : Rˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    Prod.map (coeffMap f) (coeffMap f) (nonToricPoint R p c j) =
      nonToricPoint S p (Units.map (f : R →* S) c) j := by
  simp only [nonToricPoint, Prod.map_apply, coeffMap_ofPowerSeries, slotSubst_tateUnivX_map f p c j hj hjp,
    slotSubst_tateUnivY_map f p c j hj hjp]

variable {p : ℕ} [hpr : Fact p.Prime] (hp : IsUnit (p : R)) (ζ : Rˣ)
  (hζ : ∑ i ∈ Finset.range p, (ζ : R) ^ i = 0)

include hp hζ in
theorem cuspPoint_map (v : Fin 2 → ZMod p) :
    Prod.map (coeffMap f) (coeffMap f) (cuspPoint R p ζ v) =
      cuspPoint S p (Units.map (f : R →* S) ζ) v := by
  by_cases hv : v 1 = 0
  · rw [cuspPoint_of_eq_zero ζ hv, cuspPoint_of_eq_zero _ hv, ← map_pow]
    refine tateToricPoint_map f p (ζ ^ (v 0).val) ?_
    by_cases h0 : (v 0).val = 0
    · right
      rw [h0, pow_zero, Units.val_one, sub_self]
    · left
      rw [Units.val_pow_eq_pow_val]
      refine isUnit_one_sub_pow (ζ : R) hζ hp fun hdvd => h0 ?_
      exact Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt (v 0))
  · rw [cuspPoint_of_ne_zero ζ hv, cuspPoint_of_ne_zero _ hv, ← map_pow]
    refine nonToricPoint_map f p (ζ ^ (v 0).val) (v 1).val ?_ (ZMod.val_lt (v 1))
    exact Nat.pos_of_ne_zero fun h => hv ((ZMod.val_eq_zero (v 1)).mp h)

include hp hζ in
theorem cuspData_map (v w : Fin 2 → ZMod p) :
    (cuspData R p ζ v w).map (coeffMap f) = cuspData S p (Units.map (f : R →* S) ζ) v w := by
  have hv := cuspPoint_map f hp ζ hζ v
  have hw := cuspPoint_map f hp ζ hζ w
  rw [Prod.ext_iff] at hv hw
  simp only [Prod.map_fst, Prod.map_snd] at hv hw
  exact LevelPData.ext hv.1 hv.2 hw.1 hw.2

end ModularCurve.CuspNaturalityProof

theorem solution {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (p : ℕ) [Fact p.Prime] (hp : IsUnit (p : R)) (ζ : Rˣ)
    (hζ : ∑ i ∈ Finset.range p, (ζ : R) ^ i = 0) (v w : Fin 2 → ZMod p) :
    (ModularCurve.cuspData R p ζ v w).map (ModularCurve.coeffMap f) =
      ModularCurve.cuspData S p (Units.map (f : R →* S) ζ) v w :=
  ModularCurve.CuspNaturalityProof.cuspData_map f hp ζ hζ v w

end
end S_ModularCurve_cuspData_map_coeffMap
end P2MW
export P2MW.S_ModularCurve_cuspData_map_coeffMap (solution)
