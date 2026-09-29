-- Prove2me | solution 1 for ModularCurve.coeff_zero_two_mul_cuspPoint_snd_add_fst
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/a64c41da-f4c0-5373-91e9-5af054aef018

import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Theorems.Thm_ModularCurve_coeff_slotSubst_tateUnivX
import Theorems.Thm_ModularCurve_coeff_slotSubst_tateUnivY
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_coeff_zero_two_mul_cuspPoint_snd_add_fst

set_option autoImplicit false

namespace ModularCurve
p2m_export "ModularCurve" "tateUnivX tateUnivY slotSubst nonToricPoint tateToricPoint cuspPoint cuspPoint_of_eq_zero cuspPoint_of_ne_zero coeff_slotSubst_tateUnivX coeff_slotSubst_tateUnivY"
namespace TateConst
p2m_open "ModularCurve"

p2m_open "ModularCurve P2MW.S_ModularCurve_coeff_zero_two_mul_cuspPoint_snd_add_fst.ModularCurve"

variable {K : Type*} [CommRing K]

theorem doubleSum_eq (p : ℕ) (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) (n : ℕ) (hn : n + j ≤ p) :
    (∑ M ∈ Finset.range (n + 1), ∑ e ∈ M.divisors, (e : K) *
        ((if n = p * M + j * e then (c : K) ^ e else 0) + (if n + j * e = p * M then ((c⁻¹ : Kˣ) : K) ^ e else 0)
          - (if n = p * M then 2 else 0))) =
      if n + j = p then ((c⁻¹ : Kˣ) : K) else 0 := by
  have key : ∀ M : ℕ, ∀ e ∈ M.divisors, n + j * e = p * M → M = 1 ∧ e = 1 := by
    intro M e he hE
    have heM : e ≤ M := Nat.divisor_le he
    have he1 : 1 ≤ e := Nat.pos_of_mem_divisors he
    have hM1 : M = 1 := by
      by_contra hM1
      have hM2 : 2 ≤ M := by omega
      have h1 : j * e ≤ j * M := Nat.mul_le_mul_left j heM
      nlinarith
    subst hM1
    exact ⟨rfl, le_antisymm heM he1⟩
  have hne1 : ∀ M : ℕ, ∀ e ∈ M.divisors, ¬ n = p * M + j * e := by
    intro M e he h
    have hM1 : 1 ≤ M := Nat.pos_of_ne_zero fun h0 => by simp [h0] at he
    nlinarith
  have hne3 : ∀ M : ℕ, ∀ e ∈ M.divisors, ¬ n = p * M := by
    intro M e he h
    have hM1 : 1 ≤ M := Nat.pos_of_ne_zero fun h0 => by simp [h0] at he
    nlinarith
  by_cases hnj : n + j = p
  · rw [if_pos hnj]
    have h1mem : 1 ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
    rw [Finset.sum_eq_single_of_mem 1 h1mem]
    · rw [Nat.divisors_one, Finset.sum_singleton, if_neg (hne1 1 1 (by simp)), if_neg (hne3 1 1 (by simp)),
        if_pos (by omega)]
      simp
    · intro M hM hM1
      refine Finset.sum_eq_zero fun e he => ?_
      rw [if_neg (hne1 M e he), if_neg (hne3 M e he), if_neg (fun h => hM1 (key M e he h).1)]
      simp
  · rw [if_neg hnj]
    refine Finset.sum_eq_zero fun M hM => Finset.sum_eq_zero fun e he => ?_
    rw [if_neg (hne1 M e he), if_neg (hne3 M e he), if_neg (fun h => ?_)]
    · simp
    · obtain ⟨rfl, rfl⟩ := key M e he h
      exact hnj (by simpa using h)

theorem coeff_zero_slotSubst (p : ℕ) (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    PowerSeries.coeff 0 (slotSubst K p c j tateUnivX) = 0 := by
  rw [ModularCurve.coeff_slotSubst_tateUnivX p c j hj hjp 0, doubleSum_eq p c j hj hjp 0 (by omega)]
  have h2 : ¬ (j = p) := by omega
  simp [h2]

theorem coeff_zero_slotSubst_Y (p : ℕ) (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    PowerSeries.coeff 0 (slotSubst K p c j tateUnivY) = 0 := by
  rw [ModularCurve.coeff_slotSubst_tateUnivY p c j hj hjp 0]
  have h1 : ∀ M ∈ Finset.range (0 + 1), ∀ e ∈ M.divisors, False := by
    intro M hM e he
    have : M = 0 := by simpa using hM
    subst this; simp at he
  rw [Finset.sum_eq_zero (fun M hM => Finset.sum_eq_zero fun e he => (h1 M hM e he).elim)]
  simp

end ModularCurve.TateConst

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_coeff_zero_two_mul_cuspPoint_snd_add_fst.ModularCurve ModularCurve.TateConst in
theorem solution
    (L : Type) [Field L] (N : ℕ) [NeZero N] (ξ : Lˣ) (hξ : IsPrimitiveRoot (ξ : L) N)
    (v : Fin 2 → ZMod N) (hv : v ≠ 0) :
    (2 * (ModularCurve.cuspPoint L N ξ v).2 + (ModularCurve.cuspPoint L N ξ v).1).coeff 0 =
      if v 1 = 0 then ((ξ ^ (v 0).val : Lˣ) : L) * (1 + ((ξ ^ (v 0).val : Lˣ) : L)) * ((1 - ((ξ ^ (v 0).val : Lˣ) : L))⁻¹) ^ 3
      else 0 := by
  haveI : NeZero N := inferInstance
  have hsum0 : ∀ (f g : PowerSeries L),
      (2 * HahnSeries.ofPowerSeries ℤ L g + HahnSeries.ofPowerSeries ℤ L f).coeff 0 =
        2 * PowerSeries.coeff 0 g + PowerSeries.coeff 0 f := by
    intro f g
    rw [show (2 : LaurentSeries L) = HahnSeries.ofPowerSeries ℤ L 2 from (map_ofNat _ 2).symm, ← map_mul, ← map_add,
      show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff, map_add,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, map_ofNat, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  by_cases hv1 : v 1 = 0
  · rw [if_pos hv1, ModularCurve.cuspPoint_of_eq_zero ξ hv1, ModularCurve.tateToricPoint]
    dsimp only
    rw [hsum0, PowerSeries.coeff_mk, PowerSeries.coeff_mk, if_pos rfl, if_pos rfl]
    have hv0 : v 0 ≠ 0 := by
      intro h0; apply hv; funext i; fin_cases i <;> simp [h0, hv1]
    have hne : (1 - ((ξ ^ (v 0).val : Lˣ) : L)) ≠ 0 := by
      rw [sub_ne_zero, Units.val_pow_eq_pow_val]
      intro h
      have := (hξ.pow_eq_one_iff_dvd (v 0).val).mp h.symm
      have hlt := ZMod.val_lt (v 0)
      have hpos : 0 < (v 0).val := by rwa [Nat.pos_iff_ne_zero, Ne, ZMod.val_eq_zero]
      exact absurd (Nat.le_of_dvd hpos this) (not_le.mpr hlt)
    rw [Ring.inverse_eq_inv']
    field_simp
    ring
  · rw [if_neg hv1, ModularCurve.cuspPoint_of_ne_zero ξ hv1, ModularCurve.nonToricPoint]
    dsimp only
    have hjpos : 0 < (v 1).val := by rwa [Nat.pos_iff_ne_zero, Ne, ZMod.val_eq_zero]
    rw [hsum0, coeff_zero_slotSubst N _ _ hjpos (ZMod.val_lt (v 1)), coeff_zero_slotSubst_Y N _ _ hjpos (ZMod.val_lt (v 1))]
    ring

end S_ModularCurve_coeff_zero_two_mul_cuspPoint_snd_add_fst
end P2MW
export P2MW.S_ModularCurve_coeff_zero_two_mul_cuspPoint_snd_add_fst (solution)
