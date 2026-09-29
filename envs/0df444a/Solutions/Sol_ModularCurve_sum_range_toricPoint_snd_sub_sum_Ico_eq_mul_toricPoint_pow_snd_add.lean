-- Prove2me | solution 1 for ModularCurve.sum_range_toricPoint_snd_sub_sum_Ico_eq_mul_toricPoint_pow_snd_add
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/e8019e1d-87a2-53ee-b8e1-6fbc279192e2

import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_sum_range_toricPoint_snd_sub_sum_Ico_eq_mul_toricPoint_pow_snd_add

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open ModularCurve

universe u

namespace CycloConst

section ConstB

variable {K : Type*} [Field K]

def cbY (ζ : Kˣ) (j : ℕ) : K := (1 - (ζ : K) ^ j)⁻¹

def cbP (p : ℕ) (ζ : Kˣ) (e : ℤ) : K := ∑ j ∈ Finset.Ico 1 p, cbY ζ j ^ e

theorem cb_one_sub_ne_zero {p : ℕ} {ζ : Kˣ} (hζ : IsPrimitiveRoot (ζ : K) p) {j : ℕ} (h1 : 1 ≤ j)
    (h2 : j < p) : (1 : K) - (ζ : K) ^ j ≠ 0 :=
  sub_ne_zero.mpr (Ne.symm (hζ.pow_ne_one_of_pos_of_lt (by omega) h2))

theorem cbY_ne_zero {p : ℕ} {ζ : Kˣ} (hζ : IsPrimitiveRoot (ζ : K) p) {j : ℕ} (h1 : 1 ≤ j) (h2 : j < p) :
    cbY ζ j ≠ 0 :=
  inv_ne_zero (cb_one_sub_ne_zero hζ h1 h2)

theorem cbY_inv (ζ : Kˣ) (j : ℕ) : (cbY ζ j)⁻¹ = 1 - (ζ : K) ^ j := inv_inv _

theorem cb_sum_pow {p : ℕ} {ζ : Kˣ} (hζ : IsPrimitiveRoot (ζ : K) p) (l : ℕ) (h1 : 1 ≤ l) (h2 : l ≤ p - 1) :
    ∑ j ∈ Finset.Ico 1 p, ((ζ : K) ^ j) ^ l = -1 := by
  have hp : 0 < p := by omega
  have hx1 : (ζ : K) ^ l ≠ 1 := hζ.pow_ne_one_of_pos_of_lt (by omega) (by omega)
  have hgeom : (∑ j ∈ Finset.range p, ((ζ : K) ^ l) ^ j) = 0 := by
    have h := geom_sum_mul ((ζ : K) ^ l) p
    rw [← pow_mul, mul_comm l p, pow_mul, hζ.pow_eq_one, one_pow, sub_self,
      mul_eq_zero] at h
    exact h.resolve_right (sub_ne_zero.mpr hx1)
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hp, pow_zero] at hgeom
  rw [Finset.sum_congr rfl fun (j : ℕ) _ => (pow_right_comm (ζ : K) j l)]
  linear_combination hgeom

theorem cb_sum_pow_zero {p : ℕ} (hp : 1 ≤ p) (ζ : Kˣ) :
    ∑ j ∈ Finset.Ico 1 p, ((ζ : K) ^ j) ^ 0 = (p : K) - 1 := by
  rw [Finset.sum_congr rfl fun (j : ℕ) _ => pow_zero ((ζ : K) ^ j), Finset.sum_const, Nat.card_Ico,
    nsmul_eq_mul, mul_one, Nat.cast_sub hp, Nat.cast_one]

theorem cb_alternating (n : ℕ) (hn : n ≠ 0) :
    ∑ l ∈ Finset.range (n + 1), (-1 : K) ^ l * (n.choose l : K) = 0 := by
  have h := congrArg (Int.cast : ℤ → K) (Int.alternating_sum_range_choose_of_ne hn)
  push_cast at h
  exact h

theorem cbP_neg {p : ℕ} {ζ : Kˣ} (hζ : IsPrimitiveRoot (ζ : K) p) (n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ p - 1) :
    cbP p ζ (-(n : ℤ)) = p := by
  have hp : 1 ≤ p := by omega
  unfold cbP
  rw [Finset.sum_congr rfl fun (j : ℕ) _ => by rw [zpow_neg, zpow_natCast, ← inv_pow, cbY_inv]]

  rw [Finset.sum_congr rfl fun (j : ℕ) _ => by
    rw [sub_eq_neg_add, add_pow, Finset.sum_congr rfl fun (l : ℕ) _ => by rw [one_pow, mul_one, neg_pow]]]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun (l : ℕ) _ => by rw [← Finset.sum_mul, ← Finset.mul_sum]]

  rw [Finset.sum_range_succ', pow_zero, one_mul, cb_sum_pow_zero hp, Nat.choose_zero_right, Nat.cast_one,
    mul_one]
  rw [Finset.sum_congr rfl fun (l : ℕ) hl => by
    rw [cb_sum_pow hζ (l + 1) (by omega) (by have := Finset.mem_range.mp hl; omega)]]
  have halt := cb_alternating (K := K) n (by omega)
  rw [Finset.sum_range_succ', pow_zero, one_mul, Nat.choose_zero_right, Nat.cast_one] at halt
  rw [Finset.sum_congr rfl fun (l : ℕ) _ => by rw [mul_neg_one, neg_mul]]
  rw [Finset.sum_neg_distrib]
  linear_combination (-1 : K) * halt

theorem cb_per_j {p : ℕ} {ζ : Kˣ} (hζ : IsPrimitiveRoot (ζ : K) p) {j : ℕ} (h1 : 1 ≤ j) (h2 : j < p)
    (k : ℕ) :
    ∑ i ∈ Finset.range (p + 1), (-1 : K) ^ i * (p.choose i : K) * cbY ζ j ^ ((k : ℤ) - (i : ℤ)) =
      cbY ζ j ^ (k : ℤ) := by
  have hy := cbY_ne_zero hζ h1 h2
  have key : (-(cbY ζ j)⁻¹ + 1) ^ p = 1 := by
    rw [cbY_inv, show -(1 - (ζ : K) ^ j) + 1 = (ζ : K) ^ j by ring, ← pow_mul, mul_comm, pow_mul,
      hζ.pow_eq_one, one_pow]
  have hexp := add_pow (-(cbY ζ j)⁻¹) 1 p
  rw [key] at hexp
  rw [Finset.sum_congr rfl fun (i : ℕ) _ => by
    rw [sub_eq_add_neg, zpow_add₀ hy, zpow_natCast, zpow_neg, zpow_natCast, ← inv_pow,
      show (-1 : K) ^ i * (p.choose i : K) * (cbY ζ j ^ k * (cbY ζ j)⁻¹ ^ i) =
        cbY ζ j ^ k * ((-(cbY ζ j)⁻¹) ^ i * 1 ^ (p - i) * (p.choose i : K)) by rw [neg_pow, one_pow]; ring]]
  rw [← Finset.mul_sum, ← hexp, mul_one, zpow_natCast]

theorem cb_summed {p : ℕ} {ζ : Kˣ} (hζ : IsPrimitiveRoot (ζ : K) p) (k : ℕ) :
    ∑ i ∈ Finset.range (p + 1), (-1 : K) ^ i * (p.choose i : K) * cbP p ζ ((k : ℤ) - (i : ℤ)) =
      cbP p ζ (k : ℤ) := by
  unfold cbP
  rw [Finset.sum_congr rfl fun (i : ℕ) _ => by rw [Finset.mul_sum], Finset.sum_comm]
  exact Finset.sum_congr rfl fun (j : ℕ) hj => by
    have hj' := Finset.mem_Ico.mp hj
    exact cb_per_j hζ hj'.1 hj'.2 k

theorem cb_extend (p : ℕ) (f : ℕ → K) (N : ℕ) (hN : p ≤ N) :
    ∑ i ∈ Finset.range (N + 1), (-1 : K) ^ i * (p.choose i : K) * f i =
      ∑ i ∈ Finset.range (p + 1), (-1 : K) ^ i * (p.choose i : K) * f i := by
  induction N, hN using Nat.le_induction with
  | base => rfl
  | succ N hN ih =>
    rw [Finset.sum_range_succ, ih, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero,
      zero_mul, add_zero]

theorem cb_star {p : ℕ} (hp : 1 ≤ p) {ζ : Kˣ} (hζ : IsPrimitiveRoot (ζ : K) p) (k : ℕ) (hk : 1 ≤ k) :
    ∑ i ∈ Finset.range (k + 1), (-1 : K) ^ i * (p.choose i : K) * cbP p ζ ((k : ℤ) - (i : ℤ)) =
      cbP p ζ (k : ℤ) + (p : K) * ∑ i ∈ Finset.range (k + 1), (-1 : K) ^ i * (p.choose i : K) := by
  have h1 := cb_summed hζ k
  rw [← cb_extend p (fun i => cbP p ζ ((k : ℤ) - (i : ℤ))) (p + k) (by omega)] at h1

  rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le (k + 1)) (show k + 1 ≤ p + k + 1 by omega),
    ← Finset.range_eq_Ico] at h1

  have htail : ∑ i ∈ Finset.Ico (k + 1) (p + k + 1), (-1 : K) ^ i * (p.choose i : K) * cbP p ζ ((k : ℤ) - (i : ℤ)) =
      (p : K) * ∑ i ∈ Finset.Ico (k + 1) (p + k + 1), (-1 : K) ^ i * (p.choose i : K) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun (i : ℕ) hi => ?_
    have hi' := Finset.mem_Ico.mp hi
    rcases le_or_gt i p with hip | hip
    · rw [show (k : ℤ) - (i : ℤ) = -((i - k : ℕ) : ℤ) by push_cast [Nat.cast_sub (show k ≤ i by omega)]; ring,
        cbP_neg hζ (i - k) (by omega) (by omega)]
      ring
    · rw [Nat.choose_eq_zero_of_lt hip, Nat.cast_zero, mul_zero, zero_mul, mul_zero]

  have hfull : ∑ i ∈ Finset.range (p + k + 1), (-1 : K) ^ i * (p.choose i : K) = 0 := by
    have h := cb_extend p (fun _ => (1 : K)) (p + k) (by omega)
    simp only [mul_one] at h
    rw [h]
    exact cb_alternating p (by omega)
  rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le (k + 1)) (show k + 1 ≤ p + k + 1 by omega),
    ← Finset.range_eq_Ico] at hfull
  rw [htail] at h1
  linear_combination h1 - (p : K) * hfull

theorem cbP_zero {p : ℕ} (hp : 1 ≤ p) (ζ : Kˣ) : cbP p ζ 0 = (p : K) - 1 := by
  unfold cbP
  rw [Finset.sum_congr rfl fun (j : ℕ) _ => zpow_zero (cbY ζ j), Finset.sum_const, Nat.card_Ico, nsmul_eq_mul,
    mul_one, Nat.cast_sub hp, Nat.cast_one]

theorem cb_choose_succ (p i : ℕ) : (p.choose (i + 1) : K) * (i + 1) = (p.choose i : K) * ((p : K) - i) := by
  rcases le_or_gt i p with hip | hip
  · have h := Nat.choose_succ_right_eq p i
    have h' := congrArg (Nat.cast : ℕ → K) h
    push_cast [Nat.cast_sub hip] at h'
    exact h'
  · rw [Nat.choose_eq_zero_of_lt hip, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul, zero_mul]

theorem cb_THead_eq (c : K) (hc : 1 - c ≠ 0) :
    c * (1 + 4 * c + c ^ 2) / (1 - c) ^ 4 =
      6 * ((1 - c)⁻¹) ^ 4 - 12 * ((1 - c)⁻¹) ^ 3 + 7 * ((1 - c)⁻¹) ^ 2 - (1 - c)⁻¹ := by
  field_simp
  ring

theorem cb_WHead_eq (c : K) (hc : 1 - c ≠ 0) :
    2 * c ^ 2 * (1 + 3 * c + c ^ 2) / (1 - c) ^ 6 =
      10 * ((1 - c)⁻¹) ^ 6 - 30 * ((1 - c)⁻¹) ^ 5 + 32 * ((1 - c)⁻¹) ^ 4 - 14 * ((1 - c)⁻¹) ^ 3 +
        2 * ((1 - c)⁻¹) ^ 2 := by
  field_simp
  ring

theorem cbP_closed (K : Type*) [Field K] [CharZero K] (p : ℕ) (hp : 1 ≤ p) (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) p) :
    cbP p ζ 1 = ((p : K) - 1) / 2 ∧
    cbP p ζ 2 = (-(p : K) ^ 2 + 6 * p - 5) / 12 ∧
    cbP p ζ 3 = (-(p : K) ^ 2 + 4 * p - 3) / 8 ∧
    cbP p ζ 4 = ((p : K) ^ 4 - 110 * p ^ 2 + 360 * p - 251) / 720 ∧
    cbP p ζ 5 = ((p : K) ^ 4 - 50 * p ^ 2 + 144 * p - 95) / 288 ∧
    cbP p ζ 6 = (-2 * (p : K) ^ 6 + 357 * p ^ 4 - 11508 * p ^ 2 + 30240 * p - 19087) / 60480 := by
  have hp0 : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hP0 : cbP p ζ 0 = (p : K) - 1 := cbP_zero hp ζ

  have hb1 : (p.choose 1 : K) = p := by rw [Nat.choose_one_right]
  have h2 := cb_choose_succ (K := K) p 1
  have h3 := cb_choose_succ (K := K) p 2
  have h4 := cb_choose_succ (K := K) p 3
  have h5 := cb_choose_succ (K := K) p 4
  have h6 := cb_choose_succ (K := K) p 5
  have h7 := cb_choose_succ (K := K) p 6
  rw [hb1] at h2
  push_cast at h2 h3 h4 h5 h6 h7
  have hb2 : (p.choose 2 : K) = p * (p - 1) / 2 := by
    rw [eq_div_iff (by norm_num : (2 : K) ≠ 0)]; linear_combination h2
  have hb3 : (p.choose 3 : K) = p * (p - 1) * (p - 2) / 6 := by
    rw [eq_div_iff (by norm_num : (6 : K) ≠ 0)]; rw [hb2] at h3; linear_combination 2 * h3
  have hb4 : (p.choose 4 : K) = p * (p - 1) * (p - 2) * (p - 3) / 24 := by
    rw [eq_div_iff (by norm_num : (24 : K) ≠ 0)]; rw [hb3] at h4; linear_combination 6 * h4
  have hb5 : (p.choose 5 : K) = p * (p - 1) * (p - 2) * (p - 3) * (p - 4) / 120 := by
    rw [eq_div_iff (by norm_num : (120 : K) ≠ 0)]; rw [hb4] at h5; linear_combination 24 * h5
  have hb6 : (p.choose 6 : K) = p * (p - 1) * (p - 2) * (p - 3) * (p - 4) * (p - 5) / 720 := by
    rw [eq_div_iff (by norm_num : (720 : K) ≠ 0)]; rw [hb5] at h6; linear_combination 120 * h6
  have hb7 : (p.choose 7 : K) = p * (p - 1) * (p - 2) * (p - 3) * (p - 4) * (p - 5) * (p - 6) / 5040 := by
    rw [eq_div_iff (by norm_num : (5040 : K) ≠ 0)]; rw [hb6] at h7; linear_combination 720 * h7

  have E2 := cb_star hp hζ 2 (by norm_num)
  have E3 := cb_star hp hζ 3 (by norm_num)
  have E4 := cb_star hp hζ 4 (by norm_num)
  have E5 := cb_star hp hζ 5 (by norm_num)
  have E6 := cb_star hp hζ 6 (by norm_num)
  have E7 := cb_star hp hζ 7 (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.choose_zero_right, Nat.choose_one_right,
    Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, hb2, hb3, hb4, hb5, hb6, hb7] at E2 E3 E4 E5 E6 E7
  norm_num at E2 E3 E4 E5 E6 E7
  rw [hP0] at E2 E3 E4 E5 E6 E7
  have hP1 : cbP p ζ 1 = ((p : K) - 1) / 2 := by
    rw [eq_div_iff (by norm_num : (2 : K) ≠ 0)]
    refine mul_left_cancel₀ hp0 ?_
    linear_combination (-2) * E2
  rw [hP1] at E3 E4 E5 E6 E7
  have hP2 : cbP p ζ 2 = (-(p : K) ^ 2 + 6 * p - 5) / 12 := by
    rw [eq_div_iff (by norm_num : (12 : K) ≠ 0)]
    refine mul_left_cancel₀ hp0 ?_
    linear_combination (-12) * E3
  rw [hP2] at E4 E5 E6 E7
  have hP3 : cbP p ζ 3 = (-(p : K) ^ 2 + 4 * p - 3) / 8 := by
    rw [eq_div_iff (by norm_num : (8 : K) ≠ 0)]
    refine mul_left_cancel₀ hp0 ?_
    linear_combination (-8) * E4
  rw [hP3] at E5 E6 E7
  have hP4 : cbP p ζ 4 = ((p : K) ^ 4 - 110 * p ^ 2 + 360 * p - 251) / 720 := by
    rw [eq_div_iff (by norm_num : (720 : K) ≠ 0)]
    refine mul_left_cancel₀ hp0 ?_
    linear_combination (-720) * E5
  rw [hP4] at E6 E7
  have hP5 : cbP p ζ 5 = ((p : K) ^ 4 - 50 * p ^ 2 + 144 * p - 95) / 288 := by
    rw [eq_div_iff (by norm_num : (288 : K) ≠ 0)]
    refine mul_left_cancel₀ hp0 ?_
    linear_combination (-288) * E6
  rw [hP5] at E7
  have hP6 : cbP p ζ 6 = (-2 * (p : K) ^ 6 + 357 * p ^ 4 - 11508 * p ^ 2 + 30240 * p - 19087) / 60480 := by
    rw [eq_div_iff (by norm_num : (60480 : K) ≠ 0)]
    refine mul_left_cancel₀ hp0 ?_
    linear_combination (-60480) * E7
  exact ⟨hP1, hP2, hP3, hP4, hP5, hP6⟩

theorem sum_full_THead (K : Type*) [Field K] [CharZero K] (p : ℕ) (hp : Odd p) (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) p) :
    ∑ j ∈ Finset.Ico 1 p,
        (ζ : K) ^ j * (1 + 4 * (ζ : K) ^ j + ((ζ : K) ^ j) ^ 2) / (1 - (ζ : K) ^ j) ^ 4 =
      ((p : K) ^ 4 - 1) / 120 := by
  have hp1 : 1 ≤ p := hp.pos
  obtain ⟨hP1, hP2, hP3, hP4, -, -⟩ := cbP_closed K p hp1 ζ hζ
  rw [Finset.sum_congr rfl fun (j : ℕ) hj => by
    have hj' := Finset.mem_Ico.mp hj
    rw [cb_THead_eq ((ζ : K) ^ j) (cb_one_sub_ne_zero hζ hj'.1 hj'.2)]]
  have e1 : cbP p ζ 1 = ∑ j ∈ Finset.Ico 1 p, (1 - (ζ : K) ^ j)⁻¹ := by
    unfold cbP cbY; exact Finset.sum_congr rfl fun (j : ℕ) _ => zpow_one _
  have e2 : cbP p ζ 2 = ∑ j ∈ Finset.Ico 1 p, ((1 - (ζ : K) ^ j)⁻¹) ^ 2 := by
    unfold cbP cbY; exact Finset.sum_congr rfl fun (j : ℕ) _ => zpow_ofNat _ 2
  have e3 : cbP p ζ 3 = ∑ j ∈ Finset.Ico 1 p, ((1 - (ζ : K) ^ j)⁻¹) ^ 3 := by
    unfold cbP cbY; exact Finset.sum_congr rfl fun (j : ℕ) _ => zpow_ofNat _ 3
  have e4 : cbP p ζ 4 = ∑ j ∈ Finset.Ico 1 p, ((1 - (ζ : K) ^ j)⁻¹) ^ 4 := by
    unfold cbP cbY; exact Finset.sum_congr rfl fun (j : ℕ) _ => zpow_ofNat _ 4
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, ← e1, ← e2, ← e3, ← e4, hP1, hP2, hP3, hP4]
  ring

theorem sum_full_WHead (K : Type*) [Field K] [CharZero K] (p : ℕ) (hp : Odd p) (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) p) :
    ∑ j ∈ Finset.Ico 1 p,
        2 * ((ζ : K) ^ j) ^ 2 * (1 + 3 * (ζ : K) ^ j + ((ζ : K) ^ j) ^ 2) / (1 - (ζ : K) ^ j) ^ 6 =
      -((p : K) ^ 6 - 1) / 3024 - ((p : K) ^ 4 - 1) / 1440 := by
  have hp1 : 1 ≤ p := hp.pos
  obtain ⟨-, hP2, hP3, hP4, hP5, hP6⟩ := cbP_closed K p hp1 ζ hζ
  rw [Finset.sum_congr rfl fun (j : ℕ) hj => by
    have hj' := Finset.mem_Ico.mp hj
    rw [cb_WHead_eq ((ζ : K) ^ j) (cb_one_sub_ne_zero hζ hj'.1 hj'.2)]]
  have e2 : cbP p ζ 2 = ∑ j ∈ Finset.Ico 1 p, ((1 - (ζ : K) ^ j)⁻¹) ^ 2 := by
    unfold cbP cbY; exact Finset.sum_congr rfl fun (j : ℕ) _ => zpow_ofNat _ 2
  have e3 : cbP p ζ 3 = ∑ j ∈ Finset.Ico 1 p, ((1 - (ζ : K) ^ j)⁻¹) ^ 3 := by
    unfold cbP cbY; exact Finset.sum_congr rfl fun (j : ℕ) _ => zpow_ofNat _ 3
  have e4 : cbP p ζ 4 = ∑ j ∈ Finset.Ico 1 p, ((1 - (ζ : K) ^ j)⁻¹) ^ 4 := by
    unfold cbP cbY; exact Finset.sum_congr rfl fun (j : ℕ) _ => zpow_ofNat _ 4
  have e5 : cbP p ζ 5 = ∑ j ∈ Finset.Ico 1 p, ((1 - (ζ : K) ^ j)⁻¹) ^ 5 := by
    unfold cbP cbY; exact Finset.sum_congr rfl fun (j : ℕ) _ => zpow_ofNat _ 5
  have e6 : cbP p ζ 6 = ∑ j ∈ Finset.Ico 1 p, ((1 - (ζ : K) ^ j)⁻¹) ^ 6 := by
    unfold cbP cbY; exact Finset.sum_congr rfl fun (j : ℕ) _ => zpow_ofNat _ 6
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    ← e2, ← e3, ← e4, ← e5, ← e6, hP2, hP3, hP4, hP5, hP6]
  ring

end ConstB

section Consts

variable {K : Type*} [Field K] [CharZero K]

theorem head2_eq (c : K) (hc : 1 - c ≠ 0) : c / (1 - c) ^ 2 = ((1 - c)⁻¹) ^ 2 - (1 - c)⁻¹ := by
  field_simp
  ring

theorem head3_eq (c : K) (hc : 1 - c ≠ 0) :
    c ^ 2 / (1 - c) ^ 3 = ((1 - c)⁻¹) ^ 3 - 2 * ((1 - c)⁻¹) ^ 2 + (1 - c)⁻¹ := by
  field_simp
  ring

theorem sum_div_one_sub_sq_and_sum_sq_div_one_sub_cube (p : ℕ) (hp : 1 ≤ p) (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) p) :
    ∑ j ∈ Finset.Ico 1 p, (ζ : K) ^ j / (1 - (ζ : K) ^ j) ^ 2 = -(((p : K) ^ 2 - 1) / 12) ∧
    ∑ j ∈ Finset.Ico 1 p, ((ζ : K) ^ j) ^ 2 / (1 - (ζ : K) ^ j) ^ 3 = ((p : K) ^ 2 - 1) / 24 := by
  obtain ⟨h1, h2, h3, -⟩ := cbP_closed K p hp ζ hζ
  unfold cbP cbY at h1 h2 h3
  have e1 : ∑ j ∈ Finset.Ico 1 p, (1 - (ζ : K) ^ j)⁻¹ = ((p : K) - 1) / 2 := by
    rw [← h1]; exact Finset.sum_congr rfl fun j _ => by norm_cast; rw [pow_one]
  have e2 : ∑ j ∈ Finset.Ico 1 p, ((1 - (ζ : K) ^ j)⁻¹) ^ 2 = (-(p : K) ^ 2 + 6 * p - 5) / 12 := by
    rw [← h2]; exact Finset.sum_congr rfl fun j _ => by norm_cast
  have e3 : ∑ j ∈ Finset.Ico 1 p, ((1 - (ζ : K) ^ j)⁻¹) ^ 3 = (-(p : K) ^ 2 + 4 * p - 3) / 8 := by
    rw [← h3]; exact Finset.sum_congr rfl fun j _ => by norm_cast
  have hsq : ∀ j ∈ Finset.Ico 1 p, (ζ : K) ^ j / (1 - (ζ : K) ^ j) ^ 2 = ((1 - (ζ : K) ^ j)⁻¹) ^ 2 - (1 - (ζ : K) ^ j)⁻¹ := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    exact head2_eq ((ζ : K) ^ j) (cb_one_sub_ne_zero hζ hj.1 hj.2)
  have hcu : ∀ j ∈ Finset.Ico 1 p, ((ζ : K) ^ j) ^ 2 / (1 - (ζ : K) ^ j) ^ 3 =
      ((1 - (ζ : K) ^ j)⁻¹) ^ 3 - 2 * ((1 - (ζ : K) ^ j)⁻¹) ^ 2 + (1 - (ζ : K) ^ j)⁻¹ := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    exact head3_eq ((ζ : K) ^ j) (cb_one_sub_ne_zero hζ hj.1 hj.2)
  constructor
  · rw [Finset.sum_congr rfl hsq, Finset.sum_sub_distrib, e2, e1]
    ring
  · rw [Finset.sum_congr rfl hcu, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, e3, e2, e1]
    ring

end Consts

end CycloConst

namespace DistX

section TwistB

variable {K : Type u} [Field K]

def tY (c ζ : K) (j : ℕ) : K := (1 - c * ζ ^ j)⁻¹

def tP (ℓ : ℕ) (c ζ : K) (e : ℤ) : K := ∑ j ∈ Finset.range ℓ, tY c ζ j ^ e

theorem t_one_sub_ne_zero {ℓ : ℕ} {c ζ : K} (hζ : IsPrimitiveRoot ζ ℓ) (hcℓ : c ^ ℓ ≠ 1) (j : ℕ) :
    (1 : K) - c * ζ ^ j ≠ 0 := by
  intro h
  apply hcℓ
  have h1 : c * ζ ^ j = 1 := (sub_eq_zero.mp h).symm
  have h2 : (c * ζ ^ j) ^ ℓ = 1 := by rw [h1, one_pow]
  rwa [mul_pow, ← pow_mul, mul_comm j ℓ, pow_mul, hζ.pow_eq_one, one_pow, mul_one] at h2

theorem tY_ne_zero {ℓ : ℕ} {c ζ : K} (hζ : IsPrimitiveRoot ζ ℓ) (hcℓ : c ^ ℓ ≠ 1) (j : ℕ) : tY c ζ j ≠ 0 :=
  inv_ne_zero (t_one_sub_ne_zero hζ hcℓ j)

theorem tY_inv (c ζ : K) (j : ℕ) : (tY c ζ j)⁻¹ = 1 - c * ζ ^ j := inv_inv _

theorem sum_range_pow_primitiveRoot {ℓ : ℕ} {ζ : K} (hζ : IsPrimitiveRoot ζ ℓ) (l : ℕ) :
    ∑ j ∈ Finset.range ℓ, (ζ ^ l) ^ j = if ℓ ∣ l then (ℓ : K) else 0 := by
  by_cases hpn : ℓ ∣ l
  · rw [if_pos hpn]
    obtain ⟨m, rfl⟩ := hpn
    rw [pow_mul, hζ.pow_eq_one, one_pow]
    simp
  · rw [if_neg hpn]
    have hne : ζ ^ l ≠ 1 := fun h => hpn ((hζ.pow_eq_one_iff_dvd l).mp h)
    have hgeom : (∑ j ∈ Finset.range ℓ, (ζ ^ l) ^ j) * (ζ ^ l - 1) = (ζ ^ l) ^ ℓ - 1 := geom_sum_mul _ ℓ
    rw [← pow_mul, mul_comm l ℓ, pow_mul, hζ.pow_eq_one, one_pow, sub_self] at hgeom
    exact (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr hne)

theorem t_sum_pow {ℓ : ℕ} {ζ : K} (hζ : IsPrimitiveRoot ζ ℓ) (c : K) (l : ℕ) :
    ∑ j ∈ Finset.range ℓ, (c * ζ ^ j) ^ l = c ^ l * (if ℓ ∣ l then (ℓ : K) else 0) := by
  rw [← sum_range_pow_primitiveRoot hζ l, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm j l]

theorem t_alternating (n : ℕ) (hn : n ≠ 0) :
    ∑ l ∈ Finset.range (n + 1), (-1 : K) ^ l * (n.choose l : K) = 0 := by
  have h := congrArg (Int.cast : ℤ → K) (Int.alternating_sum_range_choose_of_ne hn)
  push_cast at h
  exact h

theorem tP_neg {ℓ : ℕ} {ζ : K} (hζ : IsPrimitiveRoot ζ ℓ) (c : K) (n : ℕ) (h2 : n ≤ ℓ - 1) :
    tP ℓ c ζ (-(n : ℤ)) = ℓ := by
  unfold tP
  rw [Finset.sum_congr rfl fun (j : ℕ) _ => by rw [zpow_neg, zpow_natCast, ← inv_pow, tY_inv]]
  rw [Finset.sum_congr rfl fun (j : ℕ) _ => by
    rw [sub_eq_neg_add, add_pow, Finset.sum_congr rfl fun (l : ℕ) _ => by rw [one_pow, mul_one, neg_pow]]]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun (l : ℕ) _ => by rw [← Finset.sum_mul, ← Finset.mul_sum, t_sum_pow hζ c l]]
  rw [Finset.sum_range_succ', pow_zero, one_mul, pow_zero, one_mul, if_pos (dvd_zero ℓ), Nat.choose_zero_right,
    Nat.cast_one, mul_one]
  rw [Finset.sum_eq_zero fun (l : ℕ) hl => by
    have hl' := Finset.mem_range.mp hl
    rw [if_neg (fun h => by have := Nat.le_of_dvd (Nat.succ_pos l) h; omega), mul_zero, mul_zero, zero_mul]]
  rw [zero_add]

theorem t_per_j {ℓ : ℕ} {c ζ : K} (hζ : IsPrimitiveRoot ζ ℓ) (hcℓ : c ^ ℓ ≠ 1) (j : ℕ) (k : ℕ) :
    ∑ i ∈ Finset.range (ℓ + 1), (-1 : K) ^ i * (ℓ.choose i : K) * tY c ζ j ^ ((k : ℤ) - (i : ℤ)) =
      c ^ ℓ * tY c ζ j ^ (k : ℤ) := by
  have hy := tY_ne_zero hζ hcℓ j
  have key : (-(tY c ζ j)⁻¹ + 1) ^ ℓ = c ^ ℓ := by
    rw [tY_inv, show -(1 - c * ζ ^ j) + 1 = c * ζ ^ j by ring, mul_pow, ← pow_mul, mul_comm j ℓ, pow_mul,
      hζ.pow_eq_one, one_pow, mul_one]
  have hexp := add_pow (-(tY c ζ j)⁻¹) 1 ℓ
  rw [key] at hexp
  rw [Finset.sum_congr rfl fun (i : ℕ) _ => by
    rw [sub_eq_add_neg, zpow_add₀ hy, zpow_natCast, zpow_neg, zpow_natCast, ← inv_pow,
      show (-1 : K) ^ i * (ℓ.choose i : K) * (tY c ζ j ^ k * (tY c ζ j)⁻¹ ^ i) =
        tY c ζ j ^ k * ((-(tY c ζ j)⁻¹) ^ i * 1 ^ (ℓ - i) * (ℓ.choose i : K)) by rw [neg_pow, one_pow]; ring]]
  rw [← Finset.mul_sum, ← hexp, zpow_natCast, mul_comm]

theorem t_summed {ℓ : ℕ} {c ζ : K} (hζ : IsPrimitiveRoot ζ ℓ) (hcℓ : c ^ ℓ ≠ 1) (k : ℕ) :
    ∑ i ∈ Finset.range (ℓ + 1), (-1 : K) ^ i * (ℓ.choose i : K) * tP ℓ c ζ ((k : ℤ) - (i : ℤ)) =
      c ^ ℓ * tP ℓ c ζ (k : ℤ) := by
  unfold tP
  rw [Finset.sum_congr rfl fun (i : ℕ) _ => by rw [Finset.mul_sum], Finset.sum_comm, Finset.mul_sum]
  exact Finset.sum_congr rfl fun (j : ℕ) _ => t_per_j hζ hcℓ j k

theorem t_extend (p : ℕ) (f : ℕ → K) (N : ℕ) (hN : p ≤ N) :
    ∑ i ∈ Finset.range (N + 1), (-1 : K) ^ i * (p.choose i : K) * f i =
      ∑ i ∈ Finset.range (p + 1), (-1 : K) ^ i * (p.choose i : K) * f i := by
  induction N, hN using Nat.le_induction with
  | base => rfl
  | succ N hN ih =>
    rw [Finset.sum_range_succ, ih, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero,
      zero_mul, add_zero]

theorem t_star {ℓ : ℕ} (hp : 1 ≤ ℓ) {c ζ : K} (hζ : IsPrimitiveRoot ζ ℓ) (hcℓ : c ^ ℓ ≠ 1) (k : ℕ) (hk : 1 ≤ k) :
    ∑ i ∈ Finset.range (k + 1), (-1 : K) ^ i * (ℓ.choose i : K) * tP ℓ c ζ ((k : ℤ) - (i : ℤ)) =
      c ^ ℓ * tP ℓ c ζ (k : ℤ) + (ℓ : K) * ∑ i ∈ Finset.range (k + 1), (-1 : K) ^ i * (ℓ.choose i : K) := by
  have h1 := t_summed hζ hcℓ k
  rw [← t_extend ℓ (fun i => tP ℓ c ζ ((k : ℤ) - (i : ℤ))) (ℓ + k) (by omega)] at h1
  rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le (k + 1)) (show k + 1 ≤ ℓ + k + 1 by omega),
    ← Finset.range_eq_Ico] at h1
  have htail : ∑ i ∈ Finset.Ico (k + 1) (ℓ + k + 1), (-1 : K) ^ i * (ℓ.choose i : K) * tP ℓ c ζ ((k : ℤ) - (i : ℤ)) =
      (ℓ : K) * ∑ i ∈ Finset.Ico (k + 1) (ℓ + k + 1), (-1 : K) ^ i * (ℓ.choose i : K) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun (i : ℕ) hi => ?_
    have hi' := Finset.mem_Ico.mp hi
    rcases le_or_gt i ℓ with hip | hip
    · rw [show (k : ℤ) - (i : ℤ) = -((i - k : ℕ) : ℤ) by push_cast [Nat.cast_sub (show k ≤ i by omega)]; ring,
        tP_neg hζ c (i - k) (by omega)]
      ring
    · rw [Nat.choose_eq_zero_of_lt hip, Nat.cast_zero, mul_zero, zero_mul, mul_zero]
  have hfull : ∑ i ∈ Finset.range (ℓ + k + 1), (-1 : K) ^ i * (ℓ.choose i : K) = 0 := by
    have h := t_extend ℓ (fun _ => (1 : K)) (ℓ + k) (by omega)
    simp only [mul_one] at h
    rw [h]
    exact t_alternating ℓ (by omega)
  rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le (k + 1)) (show k + 1 ≤ ℓ + k + 1 by omega),
    ← Finset.range_eq_Ico] at hfull
  rw [htail] at h1
  linear_combination h1 - (ℓ : K) * hfull

theorem tP_zero (ℓ : ℕ) (c ζ : K) : tP ℓ c ζ 0 = (ℓ : K) := by
  unfold tP
  rw [Finset.sum_congr rfl fun (j : ℕ) _ => zpow_zero (tY c ζ j), Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_one]

theorem t_choose_succ (p i : ℕ) : (p.choose (i + 1) : K) * (i + 1) = (p.choose i : K) * ((p : K) - i) := by
  rcases le_or_gt i p with hip | hip
  · have h := Nat.choose_succ_right_eq p i
    have h' := congrArg (Nat.cast : ℕ → K) h
    push_cast [Nat.cast_sub hip] at h'
    exact h'
  · rw [Nat.choose_eq_zero_of_lt hip, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul, zero_mul]

theorem tP_closed [CharZero K] {ℓ : ℕ} (hp : 1 ≤ ℓ) {c ζ : K} (hζ : IsPrimitiveRoot ζ ℓ) (hcℓ : c ^ ℓ ≠ 1) :
    (1 - c ^ ℓ) * tP ℓ c ζ 1 = ℓ ∧
    (1 - c ^ ℓ) * tP ℓ c ζ 2 = (ℓ : K) * tP ℓ c ζ 1 + ℓ - (ℓ : K) ^ 2 ∧
    (1 - c ^ ℓ) * tP ℓ c ζ 3 = (ℓ : K) * tP ℓ c ζ 2 - (ℓ : K) * ((ℓ : K) - 1) / 2 * tP ℓ c ζ 1
      + ℓ - (ℓ : K) ^ 2 + (ℓ : K) ^ 2 * ((ℓ : K) - 1) / 2 := by
  have hP0 : tP ℓ c ζ 0 = (ℓ : K) := tP_zero ℓ c ζ
  have hb1 : (ℓ.choose 1 : K) = ℓ := by rw [Nat.choose_one_right]
  have h2 := t_choose_succ (K := K) ℓ 1
  have h3 := t_choose_succ (K := K) ℓ 2
  rw [hb1] at h2
  push_cast at h2 h3
  have hb2 : (ℓ.choose 2 : K) = ℓ * (ℓ - 1) / 2 := by
    rw [eq_div_iff (by norm_num : (2 : K) ≠ 0)]; linear_combination h2
  have hb3 : (ℓ.choose 3 : K) = ℓ * (ℓ - 1) * (ℓ - 2) / 6 := by
    rw [eq_div_iff (by norm_num : (6 : K) ≠ 0)]; rw [hb2] at h3; linear_combination 2 * h3
  have E1 := t_star hp hζ hcℓ 1 (by norm_num)
  have E2 := t_star hp hζ hcℓ 2 (by norm_num)
  have E3 := t_star hp hζ hcℓ 3 (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.choose_zero_right, Nat.choose_one_right,
    Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, hb2, hb3] at E1 E2 E3
  norm_num at E1 E2 E3
  rw [hP0] at E1 E2 E3
  refine ⟨?_, ?_, ?_⟩
  · linear_combination E1
  · linear_combination E2
  · linear_combination E3

theorem sum_orbit_heads [CharZero K] {ℓ : ℕ} (hp : 1 ≤ ℓ) {c ζ : K} (hζ : IsPrimitiveRoot ζ ℓ) (hcℓ : c ^ ℓ ≠ 1) :
    ∑ j ∈ Finset.range ℓ, c * ζ ^ j / (1 - c * ζ ^ j) ^ 2 = (ℓ : K) ^ 2 * c ^ ℓ / (1 - c ^ ℓ) ^ 2 ∧
    ∑ j ∈ Finset.range ℓ, (c * ζ ^ j) ^ 2 / (1 - c * ζ ^ j) ^ 3 =
      (ℓ : K) ^ 3 * (c ^ ℓ) ^ 2 / (1 - c ^ ℓ) ^ 3 + (ℓ : K) ^ 2 * ((ℓ : K) - 1) / 2 * (c ^ ℓ / (1 - c ^ ℓ) ^ 2) := by
  obtain ⟨h1, h2, h3⟩ := tP_closed hp hζ hcℓ
  have hD : (1 : K) - c ^ ℓ ≠ 0 := sub_ne_zero.mpr (Ne.symm hcℓ)
  unfold tP tY at h1 h2 h3
  rw [Finset.sum_congr rfl fun (j : ℕ) _ => zpow_one ((1 - c * ζ ^ j)⁻¹)] at h1 h2 h3
  rw [Finset.sum_congr rfl fun (j : ℕ) _ => show ((1 - c * ζ ^ j)⁻¹) ^ (2 : ℤ) = ((1 - c * ζ ^ j)⁻¹) ^ (2 : ℕ) by
    norm_cast] at h2 h3
  rw [Finset.sum_congr rfl fun (j : ℕ) _ => show ((1 - c * ζ ^ j)⁻¹) ^ (3 : ℤ) = ((1 - c * ζ ^ j)⁻¹) ^ (3 : ℕ) by
    norm_cast] at h3
  set S1 := ∑ j ∈ Finset.range ℓ, (1 - c * ζ ^ j)⁻¹ with hS1def
  set S2 := ∑ j ∈ Finset.range ℓ, ((1 - c * ζ ^ j)⁻¹) ^ 2 with hS2def
  set S3 := ∑ j ∈ Finset.range ℓ, ((1 - c * ζ ^ j)⁻¹) ^ 3 with hS3def
  have hS1 : S1 = (ℓ : K) / (1 - c ^ ℓ) := by
    rw [eq_div_iff hD, mul_comm]; exact h1
  have hS2 : S2 = ((ℓ : K) * S1 + ℓ - (ℓ : K) ^ 2) / (1 - c ^ ℓ) := by
    rw [eq_div_iff hD, mul_comm]; exact h2
  have hS3 : S3 = ((ℓ : K) * S2 - (ℓ : K) * ((ℓ : K) - 1) / 2 * S1 + ℓ - (ℓ : K) ^ 2 + (ℓ : K) ^ 2 * ((ℓ : K) - 1) / 2)
      / (1 - c ^ ℓ) := by
    rw [eq_div_iff hD, mul_comm]; exact h3
  have hsq : ∀ j ∈ Finset.range ℓ, c * ζ ^ j / (1 - c * ζ ^ j) ^ 2 = ((1 - c * ζ ^ j)⁻¹) ^ 2 - (1 - c * ζ ^ j)⁻¹ := by
    intro j _
    have h := t_one_sub_ne_zero hζ hcℓ j
    field_simp
    ring
  have hcu : ∀ j ∈ Finset.range ℓ, (c * ζ ^ j) ^ 2 / (1 - c * ζ ^ j) ^ 3 =
      ((1 - c * ζ ^ j)⁻¹) ^ 3 - 2 * ((1 - c * ζ ^ j)⁻¹) ^ 2 + (1 - c * ζ ^ j)⁻¹ := by
    intro j _
    have h := t_one_sub_ne_zero hζ hcℓ j
    field_simp
    ring
  constructor
  · rw [Finset.sum_congr rfl hsq, Finset.sum_sub_distrib, ← hS2def, ← hS1def, hS2, hS1]
    field_simp
    ring
  · rw [Finset.sum_congr rfl hcu, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← hS3def, ← hS2def,
      ← hS1def, hS3, hS2, hS1]
    field_simp
    ring

end TwistB

end DistX

namespace DistY

variable {K : Type u} [Field K]

def fX (p : ℕ) (u : K) (m : ℕ) : K :=
  if m = 0 then u / (1 - u) ^ 2
  else (∑ d ∈ m.divisors, if p ∣ d then ((m / d : ℕ) : K) * (u ^ (m / d) + u⁻¹ ^ (m / d)) else 0)
    - 2 * (if p ∣ m then ∑ e ∈ (m / p).divisors, (e : K) else 0)

def fY (p : ℕ) (u : K) (m : ℕ) : K :=
  if m = 0 then u ^ 2 / (1 - u) ^ 3
  else (∑ d ∈ m.divisors, if p ∣ d then
          ((m / d).choose 2 : K) * u ^ (m / d) - ((m / d + 1).choose 2 : K) * u⁻¹ ^ (m / d) else 0)
    + (if p ∣ m then ∑ e ∈ (m / p).divisors, (e : K) else 0)

theorem toricPoint_fst_eq (p : ℕ) (u : K) :
    (toricPoint K p u).1 = HahnSeries.ofPowerSeries ℤ K (PowerSeries.mk (fX p u)) := by
  rw [toricPoint_fst]
  rfl

theorem toricPoint_snd_eq (p : ℕ) (u : K) :
    (toricPoint K p u).2 = HahnSeries.ofPowerSeries ℤ K (PowerSeries.mk (fY p u)) := by
  rw [toricPoint_snd]
  rfl

def A (u : K) (k : ℕ) : K := (k.choose 2 : K) * u ^ k - ((k + 1).choose 2 : K) * u⁻¹ ^ k

def B (u : K) (k : ℕ) : K := (k : K) * (u ^ k + u⁻¹ ^ k)

theorem fY_of_ne_zero (p : ℕ) (u : K) {m : ℕ} (hm : m ≠ 0) :
    fY p u m = (∑ d ∈ m.divisors, if p ∣ d then A u (m / d) else 0) +
      (if p ∣ m then ∑ e ∈ (m / p).divisors, (e : K) else 0) := by
  unfold fY; rw [if_neg hm]; rfl

theorem fX_of_ne_zero (p : ℕ) (u : K) {m : ℕ} (hm : m ≠ 0) :
    fX p u m = (∑ d ∈ m.divisors, if p ∣ d then B u (m / d) else 0) -
      2 * (if p ∣ m then ∑ e ∈ (m / p).divisors, (e : K) else 0) := by
  unfold fX; rw [if_neg hm]; rfl

theorem fY_one_of_ne_zero (u : K) {m : ℕ} (hm : m ≠ 0) :
    fY 1 u m = ∑ k ∈ m.divisors, A u k + ∑ e ∈ m.divisors, (e : K) := by
  rw [fY_of_ne_zero 1 u hm, if_pos (one_dvd m), Nat.div_one]
  congr 1
  rw [← Nat.sum_div_divisors m (A u)]
  exact Finset.sum_congr rfl fun d _ => if_pos (one_dvd d)

theorem sum_range_pow_pow {ℓ : ℕ} {ζ : K} (hζ : IsPrimitiveRoot ζ ℓ) (k : ℕ) :
    ∑ j ∈ Finset.range ℓ, (ζ ^ j) ^ k = if ℓ ∣ k then (ℓ : K) else 0 := by
  rw [Finset.sum_congr rfl fun (j : ℕ) _ => pow_right_comm ζ j k]
  by_cases hk : ℓ ∣ k
  · rw [if_pos hk]
    obtain ⟨n, rfl⟩ := hk
    rw [pow_mul, hζ.pow_eq_one, one_pow]
    simp
  · rw [if_neg hk]
    have hne : ζ ^ k ≠ 1 := fun h => hk ((hζ.pow_eq_one_iff_dvd k).mp h)
    have hgeom : (∑ j ∈ Finset.range ℓ, (ζ ^ k) ^ j) * (ζ ^ k - 1) = (ζ ^ k) ^ ℓ - 1 := geom_sum_mul _ ℓ
    rw [← pow_mul, mul_comm k ℓ, pow_mul, hζ.pow_eq_one, one_pow, sub_self] at hgeom
    exact (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr hne)

theorem sum_range_mul_pow {ℓ : ℕ} {ζ : K} (hζ : IsPrimitiveRoot ζ ℓ) (c : K) (k : ℕ) :
    ∑ j ∈ Finset.range ℓ, (c * ζ ^ j) ^ k = c ^ k * (if ℓ ∣ k then (ℓ : K) else 0) := by
  rw [← sum_range_pow_pow hζ k, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [mul_pow]

theorem sum_range_inv_mul_pow {ℓ : ℕ} {ζ : K} (hζ : IsPrimitiveRoot ζ ℓ) (c : K) (k : ℕ) :
    ∑ j ∈ Finset.range ℓ, (c * ζ ^ j)⁻¹ ^ k = c⁻¹ ^ k * (if ℓ ∣ k then (ℓ : K) else 0) := by
  rw [← sum_range_mul_pow hζ.inv c⁻¹ k]
  exact Finset.sum_congr rfl fun j _ => by rw [mul_inv, inv_pow]

theorem sum_Ico_pow_pow {ℓ : ℕ} {ζ : K} (hζ : IsPrimitiveRoot ζ ℓ) (hℓ : 0 < ℓ) (k : ℕ) :
    ∑ j ∈ Finset.Ico 1 ℓ, (ζ ^ j) ^ k = (if ℓ ∣ k then (ℓ : K) else 0) - 1 := by
  have h := sum_range_pow_pow hζ k
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hℓ, pow_zero, one_pow] at h
  linear_combination h

theorem sum_Ico_inv_pow {ℓ : ℕ} {ζ : K} (hζ : IsPrimitiveRoot ζ ℓ) (hℓ : 0 < ℓ) (k : ℕ) :
    ∑ j ∈ Finset.Ico 1 ℓ, (ζ ^ j)⁻¹ ^ k = (if ℓ ∣ k then (ℓ : K) else 0) - 1 := by
  rw [← sum_Ico_pow_pow hζ.inv hℓ k]
  exact Finset.sum_congr rfl fun j _ => by rw [inv_pow ζ j]

theorem sum_range_A {ℓ : ℕ} {ζ : K} (hζ : IsPrimitiveRoot ζ ℓ) (c : K) (k : ℕ) :
    ∑ j ∈ Finset.range ℓ, A (c * ζ ^ j) k =
      (if ℓ ∣ k then (ℓ : K) else 0) * ((k.choose 2 : K) * c ^ k - ((k + 1).choose 2 : K) * c⁻¹ ^ k) := by
  simp only [A, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_range_mul_pow hζ, sum_range_inv_mul_pow hζ]
  ring

theorem sum_Ico_A {ℓ : ℕ} {ζ : K} (hζ : IsPrimitiveRoot ζ ℓ) (hℓ : 0 < ℓ) (k : ℕ) :
    ∑ j ∈ Finset.Ico 1 ℓ, A (ζ ^ j) k =
      ((if ℓ ∣ k then (ℓ : K) else 0) - 1) * ((k.choose 2 : K) - ((k + 1).choose 2 : K)) := by
  simp only [A, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_Ico_pow_pow hζ hℓ, sum_Ico_inv_pow hζ hℓ]
  ring

theorem choose_two_sub_choose_two_succ [CharZero K] (k : ℕ) :
    (k.choose 2 : K) - ((k + 1).choose 2 : K) = -(k : K) := by
  rw [Nat.cast_choose_two K, Nat.cast_choose_two K]
  push_cast
  ring

theorem sum_divisors_mul_ite_dvd {ℓ : ℕ} (hℓ : 0 < ℓ) (J : ℕ) (ψ : ℕ → K) :
    ∑ k ∈ (ℓ * J).divisors, (if ℓ ∣ k then ψ k else 0) = ∑ e ∈ J.divisors, ψ (ℓ * e) := by
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij' (fun d => d / ℓ) (fun e => ℓ * e) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hdm, hm0⟩, hpd⟩ := hd
    obtain ⟨e, rfl⟩ := hpd
    simp only [Nat.mul_div_cancel_left _ hℓ]
    rw [Nat.mem_divisors]
    exact ⟨(mul_dvd_mul_iff_left hℓ.ne').mp hdm, fun h => hm0 (by rw [h, mul_zero])⟩
  · intro e he
    rw [Nat.mem_divisors] at he
    rw [Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨mul_dvd_mul_left ℓ he.1, Nat.mul_ne_zero hℓ.ne' he.2⟩, dvd_mul_right ℓ e⟩
  · intro d hd
    rw [Finset.mem_filter] at hd
    obtain ⟨e, rfl⟩ := hd.2
    simp only [Nat.mul_div_cancel_left _ hℓ]
  · intro e _
    simp only [Nat.mul_div_cancel_left _ hℓ]
  · intro d hd
    rw [Finset.mem_filter] at hd
    obtain ⟨e, rfl⟩ := hd.2
    simp only [Nat.mul_div_cancel_left _ hℓ]

theorem sum_divisors_toric_dilate {ℓ : ℕ} (hℓ : 0 < ℓ) (φ : ℕ → K) (J : ℕ) :
    ∑ d ∈ (ℓ * J).divisors, (if ℓ ∣ d then φ ((ℓ * J) / d) else 0) = ∑ n ∈ J.divisors, φ n := by
  rw [sum_divisors_mul_ite_dvd hℓ J (fun d => φ ((ℓ * J) / d)), ← Nat.sum_div_divisors J φ]
  refine Finset.sum_congr rfl fun e he => ?_
  simp only [Nat.mul_div_mul_left _ _ hℓ]

theorem per_exponent [CharZero K] (ℓ : ℕ) (c : K) (k : ℕ) :
    (ℓ : K) * (A c (ℓ * k) + ((ℓ * k : ℕ) : K)) =
      (ℓ : K) ^ 3 * A (c ^ ℓ) k + (ℓ : K) ^ 2 * ((ℓ : K) - 1) / 2 * B (c ^ ℓ) k + (ℓ : K) ^ 2 * k := by
  unfold A B
  rw [← inv_pow, ← pow_mul, ← pow_mul, Nat.cast_choose_two K, Nat.cast_choose_two K, Nat.cast_choose_two K,
    Nat.cast_choose_two K]
  push_cast
  ring

theorem key [CharZero K] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (ζ : K) (hζ : IsPrimitiveRoot ζ ℓ) (c : K)
    (hc0 : c ≠ 0) (hcℓ : c ^ ℓ ≠ 1) (m : ℕ) :
    ∑ j ∈ Finset.range ℓ, fY 1 (c * ζ ^ j) m - ∑ j ∈ Finset.Ico 1 ℓ, fY 1 (ζ ^ j) m =
      (ℓ : K) ^ 3 * fY ℓ (c ^ ℓ) m + (ℓ : K) ^ 2 * ((ℓ : K) - 1) / 2 * fX ℓ (c ^ ℓ) m -
        (if m = 0 then ((ℓ : K) ^ 2 - 1) / 24 else 0) := by
  have hℓ : ℓ.Prime := Fact.out
  have hℓpos : 0 < ℓ := hℓ.pos
  have hℓ1 : 1 ≤ ℓ := hℓ.one_lt.le
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hℓ.ne_zero
  rcases eq_or_ne m 0 with rfl | hm
  ·
    simp only [fY, fX, if_true]
    set ζu : Kˣ := Units.mk0 ζ hζ0 with hζu
    have hζu' : IsPrimitiveRoot (ζu : K) ℓ := hζ
    have h2 := (CycloConst.sum_div_one_sub_sq_and_sum_sq_div_one_sub_cube ℓ hℓ1 ζu hζu').2
    simp only [hζu, Units.val_mk0] at h2
    have h1 := (DistX.sum_orbit_heads hℓ1 hζ hcℓ).2
    rw [h1, h2]
    ring
  · rw [if_neg hm, sub_zero, fY_of_ne_zero ℓ _ hm, fX_of_ne_zero ℓ _ hm,
      Finset.sum_congr rfl fun (j : ℕ) _ => fY_one_of_ne_zero (c * ζ ^ j) hm,
      Finset.sum_congr rfl fun (j : ℕ) _ => fY_one_of_ne_zero (ζ ^ j) hm,
      Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_comm, Finset.sum_const, Finset.card_range,
      Finset.sum_congr rfl fun (k : ℕ) _ => sum_range_A hζ c k]
    rw [Finset.sum_comm (s := Finset.Ico 1 ℓ), Finset.sum_const, Nat.card_Ico,
      Finset.sum_congr rfl fun (k : ℕ) _ => sum_Ico_A hζ hℓpos k]

    have hL : ∑ k ∈ m.divisors, (if ℓ ∣ k then (ℓ : K) else 0) *
          ((k.choose 2 : K) * c ^ k - ((k + 1).choose 2 : K) * c⁻¹ ^ k) +
          ℓ • ∑ e ∈ m.divisors, (e : K) -
        (∑ k ∈ m.divisors, ((if ℓ ∣ k then (ℓ : K) else 0) - 1) * ((k.choose 2 : K) - ((k + 1).choose 2 : K)) +
          (ℓ - 1) • ∑ e ∈ m.divisors, (e : K)) =
        ∑ k ∈ m.divisors, (if ℓ ∣ k then (ℓ : K) * (A c k + k) else 0) := by
      rw [nsmul_eq_mul, nsmul_eq_mul, Nat.cast_sub hℓ1, Nat.cast_one, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [choose_two_sub_choose_two_succ]
      unfold A
      split_ifs <;> ring
    rw [hL]
    by_cases hdvd : ℓ ∣ m
    · obtain ⟨J, rfl⟩ := hdvd
      rw [sum_divisors_mul_ite_dvd hℓpos J, sum_divisors_toric_dilate hℓpos, sum_divisors_toric_dilate hℓpos,
        if_pos (dvd_mul_right ℓ J), Nat.mul_div_cancel_left J hℓpos,
        Finset.sum_congr rfl fun (k : ℕ) _ => per_exponent ℓ c k, Finset.sum_add_distrib,
        Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
      ring
    · have h0 : ∀ k ∈ (m.divisors), ¬ ℓ ∣ k := fun k hk h =>
        hdvd (h.trans (Nat.mem_divisors.mp hk).1)
      rw [Finset.sum_congr rfl fun (k : ℕ) hk => if_neg (h0 k hk),
        Finset.sum_congr rfl fun (k : ℕ) hk => if_neg (h0 k hk),
        Finset.sum_congr rfl fun (k : ℕ) hk => if_neg (h0 k hk), if_neg hdvd]
      simp

end DistY

theorem solution
    (K : Type u) [Field K] [CharZero K] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2)
    (ζ : K) (hζ : IsPrimitiveRoot ζ ℓ) (c : K) (hc0 : c ≠ 0) (hcℓ : c ^ ℓ ≠ 1) :
    ∑ j ∈ Finset.range ℓ, (toricPoint K 1 (c * ζ ^ j)).2 -
        ∑ j ∈ Finset.Ico 1 ℓ, (toricPoint K 1 (ζ ^ j)).2 =
      (ℓ : LaurentSeries K) ^ 3 * (toricPoint K ℓ (c ^ ℓ)).2 +
        HahnSeries.C ((ℓ : K) ^ 2 * ((ℓ : K) - 1) / 2) * (toricPoint K ℓ (c ^ ℓ)).1 -
          HahnSeries.C (((ℓ : K) ^ 2 - 1) / 24) := by
  have hL : ∀ (s : Finset ℕ) (g : ℕ → K),
      ∑ j ∈ s, (toricPoint K 1 (g j)).2 =
        HahnSeries.ofPowerSeries ℤ K (PowerSeries.mk fun m => ∑ j ∈ s, DistY.fY 1 (g j) m) := by
    intro s g
    rw [Finset.sum_congr rfl fun j _ => DistY.toricPoint_snd_eq (K := K) 1 (g j), ← map_sum]
    congr 1
    ext m
    rw [map_sum, PowerSeries.coeff_mk]
    exact Finset.sum_congr rfl fun j _ => PowerSeries.coeff_mk _ _
  have hnat : ((ℓ : ℕ) : LaurentSeries K) = HahnSeries.C (ℓ : K) := by rw [map_natCast]
  rw [hL (Finset.range ℓ) (fun j => c * ζ ^ j), hL (Finset.Ico 1 ℓ) (fun j => ζ ^ j),
    DistY.toricPoint_snd_eq (K := K) ℓ (c ^ ℓ), DistY.toricPoint_fst_eq (K := K) ℓ (c ^ ℓ), hnat,
    ← HahnSeries.ofPowerSeries_C, ← HahnSeries.ofPowerSeries_C, ← HahnSeries.ofPowerSeries_C,
    ← map_pow, ← map_mul, ← map_mul, ← map_sub, ← map_add, ← map_sub]
  congr 1
  ext m
  rw [map_sub, map_sub, PowerSeries.coeff_mk, PowerSeries.coeff_mk, map_add, ← map_pow, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, PowerSeries.coeff_mk, PowerSeries.coeff_C]
  exact DistY.key ℓ hℓ2 ζ hζ c hc0 hcℓ m

end S_ModularCurve_sum_range_toricPoint_snd_sub_sum_Ico_eq_mul_toricPoint_pow_snd_add
end P2MW
export P2MW.S_ModularCurve_sum_range_toricPoint_snd_sub_sum_Ico_eq_mul_toricPoint_pow_snd_add (solution)
