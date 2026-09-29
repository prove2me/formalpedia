-- Prove2me | solution 1 for ModularCurve.cuspData_map_qTwist
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/69875866-200b-5775-a681-fec796af07db

import Mathlib
import Definitions.Def_ModularForm_KatzLevelOne
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Theorems.Thm_ModularCurve_coeff_slotSubst_tateUnivX
import Theorems.Thm_ModularCurve_coeff_slotSubst_tateUnivY
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_cuspData_map_qTwist

set_option autoImplicit false

universe u

p2m_open "ModularCurve P2MW.S_ModularCurve_cuspData_map_qTwist.ModularCurve HahnSeries"

namespace ModularCurve
p2m_export "ModularCurve" "LevelPData LevelPData.map_xP LevelPData.map_yP LevelPData.map_xQ LevelPData.map_yQ tateToricPoint tateToricPoint_fst tateToricPoint_snd cuspPoint cuspPoint_of_eq_zero cuspPoint_of_ne_zero cuspData cuspData_xP cuspData_yP cuspData_xQ cuspData_yQ cuspShift cuspShift_zero cuspShift_one nonToricPoint nonToricPoint_fst nonToricPoint_snd qTwist qTwist_coeff coeff_slotSubst_tateUnivX coeff_slotSubst_tateUnivY"
namespace CuspTwist
p2m_open "ModularCurve"

variable {R : Type*} [CommRing R] (p : ℕ)

section PowLemmas

variable {u ui : R} (hu : ∀ M : ℕ, u ^ (p * M) = 1) (hui : u * ui = 1)
include hu

theorem pow_eq_a {m M j e : ℕ} (h : m = p * M + j * e) : u ^ m = u ^ (j * e) := by
  rw [h, _root_.pow_add, hu, one_mul]

include hui in
theorem pow_eq_b {m M j e : ℕ} (h : m + j * e = p * M) : ui ^ (j * e) = u ^ m := by
  calc ui ^ (j * e) = ui ^ (j * e) * u ^ (p * M) := by rw [hu, mul_one]
    _ = u ^ m * (u * ui) ^ (j * e) := by rw [← h, _root_.pow_add, mul_pow]; ring
    _ = u ^ m := by rw [hui, one_pow, mul_one]

theorem pow_eq_c {m M : ℕ} (h : m = p * M) : u ^ m = 1 := by rw [h, hu]

end PowLemmas

variable (ζ : Rˣ) (hζ : ζ ^ p = 1)
include hζ

theorem hu : ∀ M : ℕ, (ζ : R) ^ (p * M) = 1 := fun M => by
  rw [pow_mul, ← Units.val_pow_eq_pow_val, hζ, Units.val_one, one_pow]

omit hζ in
theorem hui : (ζ : R) * ((ζ⁻¹ : Rˣ) : R) = 1 := by
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem qTwist_ofPowerSeries_of_support (f : PowerSeries R)
    (hf : ∀ m : ℕ, ¬ p ∣ m → PowerSeries.coeff m f = 0) :
    qTwist ζ (ofPowerSeries ℤ R f) = ofPowerSeries ℤ R f := by
  ext n
  rw [qTwist_coeff, PowerSeries.coeff_coe]
  split_ifs with hn
  · rw [mul_zero]
  · by_cases hpm : p ∣ n.natAbs
    · obtain ⟨M, hM⟩ := hpm
      have hn' : n = ((p * M : ℕ) : ℤ) := by rw [← hM]; exact (Int.natAbs_of_nonneg (not_lt.mp hn)).symm
      rw [show ((ζ ^ n : Rˣ) : R) = 1 by
        rw [hn', zpow_natCast, Units.val_pow_eq_pow_val, hu p ζ hζ M], one_mul]
    · rw [hf _ hpm, mul_zero]

theorem qTwist_tateToricPoint_fst (c : Rˣ) :
    qTwist ζ (tateToricPoint R p c).1 = (tateToricPoint R p c).1 := by
  rw [tateToricPoint_fst]
  apply qTwist_ofPowerSeries_of_support p ζ hζ
  intro m hpm
  rw [PowerSeries.coeff_mk, if_neg (by rintro rfl; exact hpm (dvd_zero p)), if_neg hpm, mul_zero, sub_zero]
  refine Finset.sum_eq_zero fun d hd => ?_
  rw [if_neg]
  exact fun hpd => hpm (hpd.trans (Nat.dvd_of_mem_divisors hd))

theorem qTwist_tateToricPoint_snd (c : Rˣ) :
    qTwist ζ (tateToricPoint R p c).2 = (tateToricPoint R p c).2 := by
  rw [tateToricPoint_snd]
  apply qTwist_ofPowerSeries_of_support p ζ hζ
  intro m hpm
  rw [PowerSeries.coeff_mk, if_neg (by rintro rfl; exact hpm (dvd_zero p)), if_neg hpm, add_zero]
  refine Finset.sum_eq_zero fun d hd => ?_
  rw [if_neg]
  exact fun hpd => hpm (hpd.trans (Nat.dvd_of_mem_divisors hd))

omit hζ in
theorem val_mul_pow_inv (c : Rˣ) (j : ℕ) :
    (((c * ζ ^ j)⁻¹ : Rˣ) : R) = ((c⁻¹ : Rˣ) : R) * ((ζ⁻¹ : Rˣ) : R) ^ j := by
  rw [mul_inv, ← inv_pow, Units.val_mul, Units.val_pow_eq_pow_val]

theorem qTwist_nonToricPoint_fst (c : Rˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    qTwist ζ (nonToricPoint R p c j).1 = (nonToricPoint R p (c * ζ ^ j) j).1 := by
  ext n
  rw [qTwist_coeff, nonToricPoint_fst, nonToricPoint_fst, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs with hn
  · rw [mul_zero]
  set m := n.natAbs with hm
  have hn' : n = (m : ℤ) := (Int.natAbs_of_nonneg (not_lt.mp hn)).symm
  rw [coeff_slotSubst_tateUnivX p c j hj hjp m, coeff_slotSubst_tateUnivX p (c * ζ ^ j) j hj hjp m, hn',
    zpow_natCast, Units.val_pow_eq_pow_val, Units.val_mul, Units.val_pow_eq_pow_val, val_mul_pow_inv ζ c j]
  have HU := hu p ζ hζ
  have HUI := hui ζ
  rw [mul_add, Finset.mul_sum]
  congr 1
  · split_ifs with hjm
    · obtain ⟨e, he⟩ := hjm
      rw [he, Nat.mul_div_cancel_left _ hj, mul_pow, ← pow_mul]; ring
    · rw [mul_zero]
  · refine Finset.sum_congr rfl fun M _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [mul_left_comm]
    congr 1
    rw [mul_sub, mul_add]
    congr 2
    · split_ifs with h
      · rw [mul_pow, ← pow_mul, pow_eq_a p HU h, mul_comm]
      · rw [mul_zero]
    · split_ifs with h
      · rw [mul_pow, ← pow_mul, pow_eq_b p HU HUI h, mul_comm]
      · rw [mul_zero]
    · split_ifs with h
      · rw [pow_eq_c p HU h, one_mul]
      · rw [mul_zero]

theorem qTwist_nonToricPoint_snd (c : Rˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    qTwist ζ (nonToricPoint R p c j).2 = (nonToricPoint R p (c * ζ ^ j) j).2 := by
  ext n
  rw [qTwist_coeff, nonToricPoint_snd, nonToricPoint_snd, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs with hn
  · rw [mul_zero]
  set m := n.natAbs with hm
  have hn' : n = (m : ℤ) := (Int.natAbs_of_nonneg (not_lt.mp hn)).symm
  rw [coeff_slotSubst_tateUnivY p c j hj hjp m, coeff_slotSubst_tateUnivY p (c * ζ ^ j) j hj hjp m, hn',
    zpow_natCast, Units.val_pow_eq_pow_val, Units.val_mul, Units.val_pow_eq_pow_val, val_mul_pow_inv ζ c j]
  have HU := hu p ζ hζ
  have HUI := hui ζ
  rw [mul_add, Finset.mul_sum]
  congr 1
  · split_ifs with hjm
    · obtain ⟨e, he⟩ := hjm
      rw [he, Nat.mul_div_cancel_left _ hj, mul_pow, ← pow_mul]; ring
    · rw [mul_zero]
  · refine Finset.sum_congr rfl fun M _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [mul_add, mul_sub]
    congr 2
    · split_ifs with h
      · rw [mul_pow, ← pow_mul, pow_eq_a p HU h]; ring
      · rw [mul_zero]
    · split_ifs with h
      · rw [mul_pow, ← pow_mul, pow_eq_b p HU HUI h]; ring
      · rw [mul_zero]
    · split_ifs with h
      · rw [pow_eq_c p HU h, one_mul]
      · rw [mul_zero]

variable [NeZero p]

theorem pow_mod_eq (x : ℕ) : ζ ^ (x % p) = ζ ^ x := by
  conv_rhs => rw [← Nat.div_add_mod x p, _root_.pow_add, pow_mul, hζ, one_pow, one_mul]

theorem pow_val_add (a b : ZMod p) : ζ ^ (a + b).val = ζ ^ a.val * ζ ^ b.val := by
  rw [ZMod.val_add, pow_mod_eq p ζ hζ, _root_.pow_add]

theorem cuspPoint_cuspShift_fst (v : Fin 2 → ZMod p) :
    qTwist ζ (cuspPoint R p ζ v).1 = (cuspPoint R p ζ (cuspShift p v)).1 := by
  by_cases hv : v 1 = 0
  · rw [cuspPoint_of_eq_zero ζ hv, cuspPoint_of_eq_zero ζ (by rw [cuspShift_one]; exact hv), cuspShift_zero,
      hv, add_zero, qTwist_tateToricPoint_fst p ζ hζ]
  · have hj : 0 < (v 1).val := Nat.pos_of_ne_zero fun h => hv ((ZMod.val_eq_zero _).mp h)
    rw [cuspPoint_of_ne_zero ζ hv, cuspPoint_of_ne_zero ζ (by rw [cuspShift_one]; exact hv), cuspShift_zero,
      cuspShift_one, qTwist_nonToricPoint_fst p ζ hζ _ _ hj (ZMod.val_lt _), pow_val_add p ζ hζ]

theorem cuspPoint_cuspShift_snd (v : Fin 2 → ZMod p) :
    qTwist ζ (cuspPoint R p ζ v).2 = (cuspPoint R p ζ (cuspShift p v)).2 := by
  by_cases hv : v 1 = 0
  · rw [cuspPoint_of_eq_zero ζ hv, cuspPoint_of_eq_zero ζ (by rw [cuspShift_one]; exact hv), cuspShift_zero,
      hv, add_zero, qTwist_tateToricPoint_snd p ζ hζ]
  · have hj : 0 < (v 1).val := Nat.pos_of_ne_zero fun h => hv ((ZMod.val_eq_zero _).mp h)
    rw [cuspPoint_of_ne_zero ζ hv, cuspPoint_of_ne_zero ζ (by rw [cuspShift_one]; exact hv), cuspShift_zero,
      cuspShift_one, qTwist_nonToricPoint_snd p ζ hζ _ _ hj (ZMod.val_lt _), pow_val_add p ζ hζ]

theorem main (v w : Fin 2 → ZMod p) :
    (cuspData R p ζ v w).map (qTwist ζ) = cuspData R p ζ (cuspShift p v) (cuspShift p w) := by
  ext
  · rw [LevelPData.map_xP, cuspData_xP, cuspData_xP, cuspPoint_cuspShift_fst p ζ hζ]
  · rw [LevelPData.map_yP, cuspData_yP, cuspData_yP, cuspPoint_cuspShift_snd p ζ hζ]
  · rw [LevelPData.map_xQ, cuspData_xQ, cuspData_xQ, cuspPoint_cuspShift_fst p ζ hζ]
  · rw [LevelPData.map_yQ, cuspData_yQ, cuspData_yQ, cuspPoint_cuspShift_snd p ζ hζ]

end ModularCurve.CuspTwist

theorem solution {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime]
    (ζ : Rˣ) (hζ : ζ ^ p = 1) (v w : Fin 2 → ZMod p) :
    (ModularCurve.cuspData R p ζ v w).map (ModularCurve.qTwist ζ)
      = ModularCurve.cuspData R p ζ (ModularCurve.cuspShift p v) (ModularCurve.cuspShift p w) :=
  ModularCurve.CuspTwist.main p ζ hζ v w

end S_ModularCurve_cuspData_map_qTwist
end P2MW
export P2MW.S_ModularCurve_cuspData_map_qTwist (solution)
