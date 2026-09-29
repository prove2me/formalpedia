-- Prove2me | solution 1 for ModularCurve.coeff_two_mul_tateUnivY_add_tateUnivX
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/14248070-4a5b-59e5-993e-722cd5a5345d

import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_coeff_two_mul_tateUnivY_add_tateUnivX

set_option autoImplicit false

open ModularCurve

namespace TatePODE

abbrev R2 := MvPowerSeries (Fin 2) ℤ

def wt (e : Fin 2 →₀ ℕ) : ℤ := (e 0 : ℤ) - (e 1 : ℤ)

theorem wt_add (e e' : Fin 2 →₀ ℕ) : wt (e + e') = wt e + wt e' := by
  simp only [wt, Finsupp.add_apply, Nat.cast_add]; ring

theorem wt_single (i k : ℕ) : wt (Finsupp.single 0 i + Finsupp.single 1 k) = (i : ℤ) - k := by
  simp [wt, Finsupp.add_apply, Finsupp.single_apply]

def D (f : R2) : R2 := fun e => wt e * MvPowerSeries.coeff e f

theorem coeff_D (e : Fin 2 →₀ ℕ) (f : R2) : MvPowerSeries.coeff e (D f) = wt e * MvPowerSeries.coeff e f := rfl

theorem D_add (f g : R2) : D (f + g) = D f + D g := by
  ext e; simp only [coeff_D, map_add]; ring

theorem D_zero : D 0 = 0 := by
  ext e; simp [coeff_D]

theorem D_mul (f g : R2) : D (f * g) = D f * g + f * D g := by
  classical
  ext e
  simp only [coeff_D, map_add, MvPowerSeries.coeff_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hpe : p.1 + p.2 = e := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rw [← hpe, wt_add]
  ring

theorem D_natCast_mul (n : ℕ) (f : R2) : D ((n : R2) * f) = (n : R2) * D f := by
  induction n with
  | zero => simp [D_zero]
  | succ m ih => rw [Nat.cast_succ, add_mul, one_mul, D_add, ih, add_mul, one_mul]

theorem D_sq (f : R2) : D (f ^ 2) = 2 * f * D f := by rw [sq, D_mul]; ring
theorem D_cube (f : R2) : D (f ^ 3) = 3 * f ^ 2 * D f := by rw [pow_succ, D_mul, D_sq]; ring

theorem coeff_natCast_mul (n : ℕ) (e : Fin 2 →₀ ℕ) (g : R2) :
    MvPowerSeries.coeff e ((n : R2) * g) = n * MvPowerSeries.coeff e g := by
  induction n with
  | zero => simp
  | succ m ih => rw [Nat.cast_succ, add_mul, one_mul, map_add, ih]; push_cast; ring

theorem D_tateUnivA4 : D tateUnivA4 = 0 := by
  ext e
  rw [coeff_D, tateUnivA4_apply, MvPowerSeries.coeff_zero]
  by_cases h : e 0 = e 1
  · rw [if_pos h]; simp [wt, h]
  · rw [if_neg h, mul_zero]

theorem D_tateUnivA6 : D tateUnivA6 = 0 := by
  ext e
  rw [coeff_D, tateUnivA6_apply, MvPowerSeries.coeff_zero]
  by_cases h : e 0 = e 1
  · rw [if_pos h]; simp [wt, h]
  · rw [if_neg h, mul_zero]

theorem two_mul_choose_two (d : ℕ) : (2 : ℤ) * (d.choose 2 : ℕ) = (d : ℤ) * ((d : ℤ) - 1) := by
  induction d with
  | zero => simp
  | succ n ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    push_cast
    linear_combination ih

theorem coeff_two_mul (e : Fin 2 →₀ ℕ) (f : R2) :
    MvPowerSeries.coeff e (2 * f) = 2 * MvPowerSeries.coeff e f := by
  rw [two_mul, map_add, two_mul]

theorem two_mul_Y_add_X : 2 * tateUnivY + tateUnivX = D tateUnivX := by
  ext e
  rw [map_add, coeff_two_mul, coeff_D, tateUnivX_apply, tateUnivY_apply]
  by_cases h : e 0 = e 1
  · rw [if_pos h, if_pos h]
    simp only [wt, h, sub_self, zero_mul]
    ring
  · rw [if_neg h, if_neg h]
    by_cases hlt : e 1 < e 0
    · rw [if_pos hlt, if_pos hlt]
      by_cases hd : e 0 - e 1 ∣ e 1
      · rw [if_pos hd, if_pos hd]
        unfold wt
        have key := two_mul_choose_two (e 0 - e 1)
        have hcast : ((e 0 - e 1 : ℕ) : ℤ) = (e 0 : ℤ) - e 1 := Nat.cast_sub hlt.le
        rw [hcast] at key ⊢
        linear_combination key
      · rw [if_neg hd, if_neg hd]; ring
    · rw [if_neg hlt, if_neg hlt]
      have hle : e 0 ≤ e 1 := not_lt.mp hlt
      by_cases hd : e 1 - e 0 ∣ e 1
      · rw [if_pos hd, if_pos hd]
        unfold wt
        have key := two_mul_choose_two (e 1 - e 0 + 1)
        have hcast : ((e 1 - e 0 : ℕ) : ℤ) = (e 1 : ℤ) - e 0 := Nat.cast_sub hle
        push_cast at key
        rw [hcast] at key ⊢
        linear_combination (-1 : ℤ) * key
      · rw [if_neg hd, if_neg hd]; ring

end TatePODE

open TatePODE in

theorem solution
    (i k : ℕ) :
    MvPowerSeries.coeff (Finsupp.single 0 i + Finsupp.single 1 k) (2 * ModularCurve.tateUnivY + ModularCurve.tateUnivX) =
      ((i : ℤ) - k) * MvPowerSeries.coeff (Finsupp.single 0 i + Finsupp.single 1 k) ModularCurve.tateUnivX := by
  have h := congrArg (MvPowerSeries.coeff (Finsupp.single 0 i + Finsupp.single 1 k)) TatePODE.two_mul_Y_add_X
  rwa [coeff_D, wt_single] at h

end S_ModularCurve_coeff_two_mul_tateUnivY_add_tateUnivX
end P2MW
export P2MW.S_ModularCurve_coeff_two_mul_tateUnivY_add_tateUnivX (solution)
