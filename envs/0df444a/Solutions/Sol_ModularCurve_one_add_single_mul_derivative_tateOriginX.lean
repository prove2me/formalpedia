-- Prove2me | solution 1 for ModularCurve.one_add_single_mul_derivative_tateOriginX
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/385cf04a-4154-5b13-a4bd-226b97507d7d

import Mathlib
import Definitions.Def_ModularCurve_TateOrigin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_one_add_single_mul_derivative_tateOriginX

set_option autoImplicit false

p2m_open "HahnSeries ModularCurve P2MW.S_ModularCurve_one_add_single_mul_derivative_tateOriginX.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "tateOriginX tateOriginY"
namespace T1
p2m_open "ModularCurve"

variable (K : Type*) [CommRing K]

noncomputable def px (k : ℕ) : PowerSeries K := PowerSeries.mk fun M =>
  if M = 0 then 0 else
    (∑ e ∈ M.divisors, (e : K) * ((e.choose k : K) + (-1) ^ k * ((e + k - 1).choose k : K)))
      - (if k = 0 then 2 * ∑ e ∈ M.divisors, (e : K) else 0)

noncomputable def py (k : ℕ) : PowerSeries K := PowerSeries.mk fun M =>
  if M = 0 then 0 else
    (∑ e ∈ M.divisors, ((e.choose 2 : K) * (e.choose k : K)
        - ((e + 1).choose 2 : K) * ((-1) ^ k * ((e + k - 1).choose k : K))))
      + (if k = 0 then ∑ e ∈ M.divisors, (e : K) else 0)

theorem tateOriginX_eq : tateOriginX K = single (-2 : ℤ) (1 : PowerSeries K) + single (-1 : ℤ) 1 +
    HahnSeries.ofPowerSeries ℤ (PowerSeries K) (PowerSeries.mk (px K)) := rfl

theorem tateOriginY_eq : tateOriginY K = single (-3 : ℤ) (-1 : PowerSeries K) + single (-2 : ℤ) (-2) + single (-1 : ℤ) (-1) +
    HahnSeries.ofPowerSeries ℤ (PowerSeries K) (PowerSeries.mk (py K)) := rfl

variable {K}

theorem coeff_derivative (x : LaurentSeries (PowerSeries K)) (n : ℤ) :
    (LaurentSeries.derivative (PowerSeries K) x).coeff n = ((n + 1 : ℤ) : PowerSeries K) * x.coeff (n + 1) := by
  rw [LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_coeff, Ring.choose_one_right, zsmul_eq_mul]
  push_cast
  ring_nf

theorem coeff_single_one_mul (x : LaurentSeries (PowerSeries K)) (n : ℤ) :
    (single (1 : ℤ) (1 : PowerSeries K) * x).coeff n = x.coeff (n - 1) := by
  have h := HahnSeries.coeff_single_mul_add (r := (1 : PowerSeries K)) (x := x) (a := n - 1) (b := (1 : ℤ))
  rw [sub_add_cancel, one_mul] at h
  exact h

theorem coeff_X (n : ℤ) : (tateOriginX K).coeff n =
    (if n = -2 then 1 else 0) + (if n = -1 then 1 else 0) + (if n < 0 then 0 else px K n.natAbs) := by
  rw [tateOriginX_eq, HahnSeries.coeff_add, HahnSeries.coeff_add, HahnSeries.coeff_single, HahnSeries.coeff_single,
    PowerSeries.coeff_coe, PowerSeries.coeff_mk]
  split_ifs <;> rfl

theorem coeff_Y (n : ℤ) : (tateOriginY K).coeff n =
    (if n = -3 then -1 else 0) + (if n = -2 then -2 else 0) + (if n = -1 then -1 else 0) + (if n < 0 then 0 else py K n.natAbs) := by
  rw [tateOriginY_eq, HahnSeries.coeff_add, HahnSeries.coeff_add, HahnSeries.coeff_add, HahnSeries.coeff_single,
    HahnSeries.coeff_single, HahnSeries.coeff_single, PowerSeries.coeff_coe, PowerSeries.coeff_mk]
  split_ifs <;> rfl

theorem binom1 (e k : ℕ) :
    ((k + 1 : ℕ) : K) * (e : K) * (e.choose (k + 1) : K) + ((k : K) - 1) * (e : K) * (e.choose k : K)
      = 2 * (e.choose 2 : K) * (e.choose k : K) := by
  have h1 : (e.choose (k + 1) * (k + 1) : ℕ) = e.choose k * (e - k) := Nat.choose_succ_right_eq e k
  have h2 : (e.choose 2 * 2 : ℕ) = e.choose 1 * (e - 1) := Nat.choose_succ_right_eq e 1
  rw [Nat.choose_one_right] at h2
  rcases Nat.lt_or_ge e k with hke | hke
  · rw [Nat.choose_eq_zero_of_lt hke, Nat.choose_eq_zero_of_lt (by omega)]
    simp
  · have h1' : ((k + 1 : ℕ) : K) * (e.choose (k + 1) : K) = (e.choose k : K) * ((e : K) - k) := by
      have := congrArg (Nat.cast (R := K)) h1
      push_cast [Nat.cast_sub hke] at this ⊢
      linear_combination this
    rcases Nat.eq_zero_or_pos e with he | he
    · subst he; simp
    · have h2' : 2 * (e.choose 2 : K) = (e : K) * ((e : K) - 1) := by
        have := congrArg (Nat.cast (R := K)) h2
        push_cast [Nat.cast_sub he] at this
        linear_combination this
      linear_combination (e : K) * h1' - (e.choose k : K) * h2'

theorem binom2 (e k : ℕ) (he : 1 ≤ e) :
    ((k + 1 : ℕ) : K) * (e : K) * ((-1) ^ (k + 1) * ((e + (k + 1) - 1).choose (k + 1) : K))
      + ((k : K) - 1) * (e : K) * ((-1) ^ k * ((e + k - 1).choose k : K))
      = 2 * (-(((e + 1).choose 2 : K) * ((-1) ^ k * ((e + k - 1).choose k : K)))) := by

  have h1 : ((e + k - 1 + 1) * (e + k - 1).choose k : ℕ) = (e + k - 1 + 1).choose (k + 1) * (k + 1) :=
    Nat.add_one_mul_choose_eq (e + k - 1) k
  have he1 : e + k - 1 + 1 = e + k := by omega
  rw [he1] at h1
  have h1' : ((k + 1 : ℕ) : K) * ((e + (k + 1) - 1).choose (k + 1) : K) = ((e : K) + k) * ((e + k - 1).choose k : K) := by
    rw [show e + (k + 1) - 1 = e + k by omega]
    have := congrArg (Nat.cast (R := K)) h1
    push_cast at this ⊢
    linear_combination -this
  have h2 : ((e + 1).choose 2 * 2 : ℕ) = (e + 1).choose 1 * (e + 1 - 1) := Nat.choose_succ_right_eq (e + 1) 1
  rw [Nat.choose_one_right, Nat.add_sub_cancel] at h2
  have h2' : 2 * ((e + 1).choose 2 : K) = ((e : K) + 1) * (e : K) := by
    have := congrArg (Nat.cast (R := K)) h2
    push_cast at this
    linear_combination this
  rw [pow_succ]
  linear_combination (e : K) * ((-1 : K) ^ k * (-1)) * h1' + ((-1 : K) ^ k * ((e + k - 1).choose k : K)) * h2'

theorem keysum (k M : ℕ) (hM : M ≠ 0) :
    ((k + 1 : ℕ) : K) * PowerSeries.coeff M (px K (k + 1)) + (k : K) * PowerSeries.coeff M (px K k)
      = 2 * PowerSeries.coeff M (py K k) + PowerSeries.coeff M (px K k) := by
  simp only [px, py, PowerSeries.coeff_mk, if_neg hM, if_neg (Nat.succ_ne_zero k)]
  have hcore : ((k + 1 : ℕ) : K) * (∑ e ∈ M.divisors, (e : K) * ((e.choose (k + 1) : K) + (-1) ^ (k + 1) * ((e + (k + 1) - 1).choose (k + 1) : K)))
      + ((k : K) - 1) * (∑ e ∈ M.divisors, (e : K) * ((e.choose k : K) + (-1) ^ k * ((e + k - 1).choose k : K)))
      - 2 * (∑ e ∈ M.divisors, ((e.choose 2 : K) * (e.choose k : K) - ((e + 1).choose 2 : K) * ((-1) ^ k * ((e + k - 1).choose k : K)))) = 0 := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_eq_zero fun e he => ?_
    have he1 : 1 ≤ e := Nat.pos_of_mem_divisors he
    linear_combination binom1 (K := K) e k + binom2 (K := K) e k he1
  by_cases hk : k = 0
  · subst hk
    simp only [if_true, sub_zero, Nat.cast_zero, zero_mul, add_zero] at hcore ⊢
    linear_combination hcore
  · simp only [if_neg hk, sub_zero, add_zero]
    linear_combination hcore

theorem main : (1 + HahnSeries.single (1 : ℤ) (1 : PowerSeries K)) * LaurentSeries.derivative (PowerSeries K) (tateOriginX K)
      = 2 * tateOriginY K + tateOriginX K := by
  apply HahnSeries.ext; funext n
  rw [add_mul, one_mul, HahnSeries.coeff_add, coeff_single_one_mul, coeff_derivative, coeff_derivative,
    show n - 1 + 1 = n by ring, HahnSeries.coeff_add,
    show (2 : LaurentSeries (PowerSeries K)) = HahnSeries.C (2 : PowerSeries K) by rw [map_ofNat],
    HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul, coeff_X, coeff_X, coeff_Y]

  rcases lt_or_ge n 0 with hneg | hpos
  · have h5 : n < -3 ∨ n = -3 ∨ n = -2 ∨ n = -1 := by omega
    rcases h5 with h | rfl | rfl | rfl
    · rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
        if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
      ring
    · norm_num
    · norm_num
    · norm_num

  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k := ⟨n.toNat, by omega⟩
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    show ((k : ℤ) + 1).natAbs = k + 1 by omega, show ((k : ℤ)).natAbs = k by omega]
  simp only [zero_add]
  have h := keysum (K := K) k
  ext M
  rw [map_add, map_add, ← map_intCast (PowerSeries.C (R := K)), ← map_intCast (PowerSeries.C (R := K)), PowerSeries.coeff_C_mul,
    PowerSeries.coeff_C_mul, ← map_ofNat (PowerSeries.C (R := K)) 2, PowerSeries.coeff_C_mul]
  by_cases hM : M = 0
  · subst hM; simp [px, py]
  · have h' := h M hM
    push_cast at h' ⊢
    linear_combination h'

end ModularCurve.T1

theorem solution (K : Type*) [CommRing K] :
    (1 + HahnSeries.single (1 : ℤ) (1 : PowerSeries K)) * LaurentSeries.derivative (PowerSeries K) (ModularCurve.tateOriginX K)
      = 2 * ModularCurve.tateOriginY K + ModularCurve.tateOriginX K :=
  ModularCurve.T1.main

end S_ModularCurve_one_add_single_mul_derivative_tateOriginX
end P2MW
export P2MW.S_ModularCurve_one_add_single_mul_derivative_tateOriginX (solution)
