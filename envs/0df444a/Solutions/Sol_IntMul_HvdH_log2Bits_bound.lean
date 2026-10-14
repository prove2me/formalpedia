-- Prove2me | solution 1 for IntMul.HvdH.log2Bits_bound
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-11T21:48:15.081743+00:00
-- url     : https://prove2.me/submissions/cfa023fd-8260-402d-85ea-7f74f897a51e

import Definitions.Def_IntMul_HvdH_Numeric

open Finset

namespace IntMul.HvdH.Num
open IntMul.HvdH

/-- Truncating a convergent series after `K` terms and perturbing each kept term by at most `1`
costs at most `K` plus the size of the tail. -/
lemma trunc_bound (f : ℕ → ℝ) (a : ℝ) (hf : HasSum f a) (c : ℕ → ℝ) (K : ℕ)
    (hc : ∀ k, |c k - f k| ≤ 1) (B : ℝ) (htail : |∑' i, f (i + K)| ≤ B) :
    |∑ k ∈ range K, c k - a| ≤ K + B := by
  rw [← hf.tsum_eq, ← hf.summable.sum_add_tsum_nat_add K]
  have h1 : |∑ k ∈ range K, (c k - f k)| ≤ K := by
    calc |∑ k ∈ range K, (c k - f k)| ≤ ∑ k ∈ range K, |c k - f k| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k ∈ range K, (1 : ℝ) := Finset.sum_le_sum (fun k _ => hc k)
      _ = K := by simp
  rw [Finset.sum_sub_distrib] at h1
  calc |∑ k ∈ range K, c k - (∑ i ∈ range K, f i + ∑' i, f (i + K))|
      = |(∑ k ∈ range K, c k - ∑ k ∈ range K, f k) - ∑' i, f (i + K)| := by
        rw [sub_add_eq_sub_sub]
    _ ≤ |∑ k ∈ range K, c k - ∑ k ∈ range K, f k| + |∑' i, f (i + K)| := abs_sub _ _
    _ ≤ K + B := add_le_add h1 htail

lemma natdiv_bound (m n : ℕ) (hn : 0 < n) : |((m / n : ℕ) : ℝ) - (m : ℝ) / n| ≤ 1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : ((m / n : ℕ) : ℝ) * n ≤ m := by exact_mod_cast Nat.div_mul_le_self m n
  have h2 : (m : ℝ) < ((m / n : ℕ) + 1 : ℝ) * n := by
    have := Nat.lt_mul_div_succ m hn
    have : (m : ℝ) < (n : ℝ) * ((m / n : ℕ) + 1 : ℝ) := by exact_mod_cast this
    linarith
  have h3 : (m : ℝ) / n < (m / n : ℕ) + 1 := by rw [div_lt_iff₀ hn']; linarith
  have h4 : ((m / n : ℕ) : ℝ) ≤ m / n := by rw [le_div_iff₀ hn']; linarith
  rw [abs_le]; constructor <;> linarith

lemma hasSum_real_arctan {x : ℝ} (hx : |x| < 1) :
    HasSum (fun n : ℕ => (-1) ^ n * x ^ (2 * n + 1) / (2 * n + 1)) (Real.arctan x) := by
  have h := Complex.hasSum_arctan (z := (x : ℂ)) (by rwa [Complex.norm_real, Real.norm_eq_abs])
  rw [← Complex.ofReal_arctan] at h
  refine Complex.hasSum_ofReal.1 ?_
  convert h using 2 with n
  push_cast; ring

theorem atanInv_bound (x N K : ℕ) (hx : 2 ≤ x) :
    |(atanInv x N K : ℝ) - 2 ^ N * Real.arctan (1 / x)| ≤ K + 2 * 2 ^ N / x ^ (2 * K + 1) := by
  have hx0 : (2 : ℝ) ≤ x := by exact_mod_cast hx
  have hxp : (0 : ℝ) < x := by linarith
  have hq : |(1 : ℝ) / x| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one hxp]; linarith
  set f : ℕ → ℝ := fun n => 2 ^ N * ((-1) ^ n * (1 / (x : ℝ)) ^ (2 * n + 1) / (2 * n + 1)) with hf
  have hs : HasSum f (2 ^ N * Real.arctan (1 / x)) := (hasSum_real_arctan hq).mul_left _
  have hcast : (atanInv x N K : ℝ) = ∑ k ∈ range K,
      (-1) ^ k * ((2 ^ N / ((2 * k + 1) * x ^ (2 * k + 1)) : ℕ) : ℝ) := by
    unfold atanInv; push_cast; rfl
  rw [hcast]
  refine trunc_bound f _ hs _ K (fun k => ?_) _ ?_
  · have hd : 0 < (2 * k + 1) * x ^ (2 * k + 1) := by positivity
    have hb := natdiv_bound (2 ^ N) ((2 * k + 1) * x ^ (2 * k + 1)) hd
    have e : f k = (-1) ^ k * (((2 ^ N : ℕ) : ℝ) / (((2 * k + 1) * x ^ (2 * k + 1) : ℕ) : ℝ)) := by
      rw [hf]; push_cast; rw [one_div_pow]; field_simp
    rw [e, ← mul_sub, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    exact hb
  · -- geometric tail bound
    set r : ℝ := 1 / (x : ℝ) ^ 2 with hr
    have hr0 : 0 ≤ r := by positivity
    have hr1 : r ≤ 1 / 4 := by
      rw [hr, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    set g : ℕ → ℝ := fun i => 2 ^ N / (x : ℝ) ^ (2 * K + 1) * r ^ i with hg
    have hgs : HasSum g (2 ^ N / (x : ℝ) ^ (2 * K + 1) * (1 - r)⁻¹) :=
      (hasSum_geometric_of_lt_one hr0 (by linarith)).mul_left _
    have hb : ‖∑' i, f (i + K)‖ ≤ 2 ^ N / (x : ℝ) ^ (2 * K + 1) * (1 - r)⁻¹ := by
      refine tsum_of_norm_bounded hgs (fun i => ?_)
      rw [hf, hg, Real.norm_eq_abs]
      have hpos : (0 : ℝ) < 2 * ((i + K : ℕ) : ℝ) + 1 := by positivity
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ N), abs_div, abs_mul, abs_pow,
        abs_neg, abs_one, one_pow, one_mul, abs_of_pos hpos, abs_pow,
        abs_of_pos (by positivity : (0 : ℝ) < 1 / x)]
      have e : (1 / (x : ℝ)) ^ (2 * (i + K) + 1) = 1 / (x : ℝ) ^ (2 * K + 1) * r ^ i := by
        rw [hr, one_div_pow, one_div_pow, ← pow_mul, div_mul_div_comm, one_mul,
          ← pow_add]; congr 2; ring
      rw [e]; simp only []
      rw [← mul_div_assoc, div_le_iff₀ hpos]
      have : 0 ≤ 2 ^ N * (1 / (x : ℝ) ^ (2 * K + 1) * r ^ i) := by positivity
      have h1 : (1 : ℝ) ≤ 2 * ((i + K : ℕ) : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) (i + K); linarith
      calc 2 ^ N * (1 / (x : ℝ) ^ (2 * K + 1) * r ^ i)
          = 2 ^ N / (x : ℝ) ^ (2 * K + 1) * r ^ i * 1 := by ring
        _ ≤ 2 ^ N / (x : ℝ) ^ (2 * K + 1) * r ^ i * (2 * ((i + K : ℕ) : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
    rw [Real.norm_eq_abs] at hb
    refine hb.trans ?_
    have : (1 - r)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    calc 2 ^ N / (x : ℝ) ^ (2 * K + 1) * (1 - r)⁻¹ ≤ 2 ^ N / (x : ℝ) ^ (2 * K + 1) * 2 :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = 2 * 2 ^ N / x ^ (2 * K + 1) := by ring

lemma hasSum_real_atanh {x : ℝ} (hx : |x| < 1) :
    HasSum (fun n : ℕ => x ^ (2 * n + 1) / (2 * n + 1))
      ((Real.log (1 + x) - Real.log (1 - x)) / 2) := by
  have h := (Real.hasSum_log_sub_log_of_abs_lt_one hx).div_const 2
  have e : (fun n : ℕ => x ^ (2 * n + 1) / (2 * n + 1)) =
      (fun i : ℕ => 2 * (1 / (2 * (i : ℝ) + 1)) * x ^ (2 * i + 1) / 2) := by
    funext n; field_simp
  rw [e]; exact h

theorem atanhInv_bound (x N K : ℕ) (hx : 2 ≤ x) :
    |(atanhInv x N K : ℝ) - 2 ^ N * ((Real.log (1 + 1 / x) - Real.log (1 - 1 / x)) / 2)| ≤ K + 2 * 2 ^ N / x ^ (2 * K + 1) := by
  have hx0 : (2 : ℝ) ≤ x := by exact_mod_cast hx
  have hxp : (0 : ℝ) < x := by linarith
  have hq : |(1 : ℝ) / x| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one hxp]; linarith
  set f : ℕ → ℝ := fun n => 2 ^ N * ((1 / (x : ℝ)) ^ (2 * n + 1) / (2 * n + 1)) with hf
  have hs : HasSum f (2 ^ N * ((Real.log (1 + 1 / x) - Real.log (1 - 1 / x)) / 2)) := (hasSum_real_atanh hq).mul_left _
  have hcast : (atanhInv x N K : ℝ) = ∑ k ∈ range K,
      ((2 ^ N / ((2 * k + 1) * x ^ (2 * k + 1)) : ℕ) : ℝ) := by
    unfold atanhInv; push_cast; rfl
  rw [hcast]
  refine trunc_bound f _ hs _ K (fun k => ?_) _ ?_
  · have hd : 0 < (2 * k + 1) * x ^ (2 * k + 1) := by positivity
    have hb := natdiv_bound (2 ^ N) ((2 * k + 1) * x ^ (2 * k + 1)) hd
    have e : f k = (((2 ^ N : ℕ) : ℝ) / (((2 * k + 1) * x ^ (2 * k + 1) : ℕ) : ℝ)) := by
      rw [hf]; push_cast; rw [one_div_pow]; field_simp
    rw [e]
    exact hb
  · -- geometric tail bound
    set r : ℝ := 1 / (x : ℝ) ^ 2 with hr
    have hr0 : 0 ≤ r := by positivity
    have hr1 : r ≤ 1 / 4 := by
      rw [hr, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    set g : ℕ → ℝ := fun i => 2 ^ N / (x : ℝ) ^ (2 * K + 1) * r ^ i with hg
    have hgs : HasSum g (2 ^ N / (x : ℝ) ^ (2 * K + 1) * (1 - r)⁻¹) :=
      (hasSum_geometric_of_lt_one hr0 (by linarith)).mul_left _
    have hb : ‖∑' i, f (i + K)‖ ≤ 2 ^ N / (x : ℝ) ^ (2 * K + 1) * (1 - r)⁻¹ := by
      refine tsum_of_norm_bounded hgs (fun i => ?_)
      rw [hf, hg, Real.norm_eq_abs]
      have hpos : (0 : ℝ) < 2 * ((i + K : ℕ) : ℝ) + 1 := by positivity
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ N), abs_div, abs_of_pos hpos, abs_pow,
        abs_of_pos (by positivity : (0 : ℝ) < 1 / x)]
      have e : (1 / (x : ℝ)) ^ (2 * (i + K) + 1) = 1 / (x : ℝ) ^ (2 * K + 1) * r ^ i := by
        rw [hr, one_div_pow, one_div_pow, ← pow_mul, div_mul_div_comm, one_mul,
          ← pow_add]; congr 2; ring
      rw [e]; simp only []
      rw [← mul_div_assoc, div_le_iff₀ hpos]
      have : 0 ≤ 2 ^ N * (1 / (x : ℝ) ^ (2 * K + 1) * r ^ i) := by positivity
      have h1 : (1 : ℝ) ≤ 2 * ((i + K : ℕ) : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) (i + K); linarith
      calc 2 ^ N * (1 / (x : ℝ) ^ (2 * K + 1) * r ^ i)
          = 2 ^ N / (x : ℝ) ^ (2 * K + 1) * r ^ i * 1 := by ring
        _ ≤ 2 ^ N / (x : ℝ) ^ (2 * K + 1) * r ^ i * (2 * ((i + K : ℕ) : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
    rw [Real.norm_eq_abs] at hb
    refine hb.trans ?_
    have : (1 - r)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    calc 2 ^ N / (x : ℝ) ^ (2 * K + 1) * (1 - r)⁻¹ ≤ 2 ^ N / (x : ℝ) ^ (2 * K + 1) * 2 :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = 2 * 2 ^ N / x ^ (2 * K + 1) := by ring

lemma two_pow_le_pow (x M : ℕ) (hx : 2 ≤ x) : (2 : ℝ) ^ M ≤ (x : ℝ) ^ (2 * M + 1) := by
  have hx' : (2 : ℝ) ≤ x := by exact_mod_cast hx
  calc (2 : ℝ) ^ M ≤ (x : ℝ) ^ M := pow_le_pow_left₀ (by norm_num) hx' M
    _ ≤ (x : ℝ) ^ (2 * M + 1) := pow_le_pow_right₀ (by linarith) (by omega)

theorem piApprox_bound (M : ℕ) : |(piApprox M : ℝ) - 2 ^ M * Real.pi| ≤ 20 * M + 40 := by
  have h5 := atanInv_bound 5 M M (by norm_num)
  have h239 := atanInv_bound 239 M M (by norm_num)
  have e5 : (2 : ℝ) * 2 ^ M / ((5 : ℕ) : ℝ) ^ (2 * M + 1) ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have := two_pow_le_pow 5 M (by norm_num); nlinarith
  have e239 : (2 : ℝ) * 2 ^ M / ((239 : ℕ) : ℝ) ^ (2 * M + 1) ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have := two_pow_le_pow 239 M (by norm_num); nlinarith
  have hm := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  have hpi : 2 ^ M * Real.pi = 16 * (2 ^ M * Real.arctan (1 / ((5 : ℕ) : ℝ)))
      - 4 * (2 ^ M * Real.arctan (1 / ((239 : ℕ) : ℝ))) := by
    simp only [one_div, Nat.cast_ofNat]; linear_combination (-4 * 2 ^ M : ℝ) * hm
  have hc : (piApprox M : ℝ) = 16 * (atanInv 5 M M : ℝ) - 4 * (atanInv 239 M M : ℝ) := by
    unfold piApprox; push_cast; ring
  rw [hc, hpi]
  rw [abs_le] at h5 h239 ⊢
  constructor <;> nlinarith [h5.1, h5.2, h239.1, h239.2]

lemma pow_bound (n : ℕ) : (80 * n + 440 : ℝ) ≤ 512 * 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ k ih =>
    push_cast
    have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    rw [pow_succ]; nlinarith

/-- Rounding `P / 2^s` to the nearest integer (`(P + 2^{s-1}) / 2^s`, floor division). -/
lemma round_bound (P : ℤ) (s : ℕ) :
    |(((P + 2 ^ s) / 2 ^ (s + 1) : ℤ) : ℝ) - (P : ℝ) / 2 ^ (s + 1)| ≤ 1 / 2 := by
  set q := (P + 2 ^ s) / 2 ^ (s + 1)
  have hd : (0 : ℤ) < 2 ^ (s + 1) := by positivity
  have h1 : q * 2 ^ (s + 1) ≤ P + 2 ^ s := Int.ediv_mul_le _ hd.ne'
  have h2 : P + 2 ^ s < (q + 1) * 2 ^ (s + 1) := by
    have := Int.lt_ediv_add_one_mul_self (P + 2 ^ s) hd; linarith
  have h1' : (q : ℝ) * 2 ^ (s + 1) ≤ P + 2 ^ s := by exact_mod_cast h1
  have h2' : (P : ℝ) + 2 ^ s < (q + 1) * 2 ^ (s + 1) := by exact_mod_cast h2
  have hp : (0 : ℝ) < 2 ^ (s + 1) := by positivity
  have hs : (2 : ℝ) ^ (s + 1) = 2 * 2 ^ s := by ring
  have e : (q : ℝ) - P / 2 ^ (s + 1) = ((q : ℝ) * 2 ^ (s + 1) - P) / 2 ^ (s + 1) := by
    field_simp
  rw [e, abs_div, abs_of_pos hp, div_le_iff₀ hp, abs_le]
  constructor <;> nlinarith

/-- Rounding a `2n+9`-bit approximation with error `≤ 20(2n+9)+40` gives an `n`-bit one. -/
lemma bits_bound (A : ℤ) (c : ℝ) (n : ℕ)
    (ha : |(A : ℝ) - 2 ^ (2 * n + 9) * c| ≤ 20 * ((2 * n + 9 : ℕ) : ℝ) + 40) :
    |(((A + 2 ^ (n + 8)) / 2 ^ (n + 9) : ℤ) : ℝ) - 2 ^ n * c| ≤ 1 := by
  have hr := round_bound (A) (n + 8)
  have hp : (0 : ℝ) < 2 ^ (n + 9) := by positivity
  have hpb := pow_bound n
  have e : (2 : ℝ) ^ (2 * n + 9) = 2 ^ (n + 9) * 2 ^ n := by rw [← pow_add]; congr 1; omega
  set u : ℝ := (((A + 2 ^ (n + 8)) / 2 ^ (n + 8 + 1) : ℤ) : ℝ)
  set P : ℝ := (A : ℝ) with hP
  have hq : |P / 2 ^ (n + 9) - 2 ^ n * c| ≤ 1 / 2 := by
    rw [show P / 2 ^ (n + 9) - 2 ^ n * c = (P - 2 ^ (2 * n + 9) * c) / 2 ^ (n + 9) by
      rw [e]; field_simp]
    rw [abs_div, abs_of_pos hp, div_le_iff₀ hp]
    refine ha.trans ?_
    push_cast
    have : (2 : ℝ) ^ (n + 9) = 512 * 2 ^ n := by ring
    rw [this]; linarith
  have hr' : |u - P / 2 ^ (n + 9)| ≤ 1 / 2 := hr
  calc |u - 2 ^ n * c| = |(u - P / 2 ^ (n + 9)) + (P / 2 ^ (n + 9) - 2 ^ n * c)| := by ring_nf
    _ ≤ |u - P / 2 ^ (n + 9)| + |P / 2 ^ (n + 9) - 2 ^ n * c| := abs_add_le _ _
    _ ≤ 1 := by linarith

theorem piBits_bound (n : ℕ) : |(piBits n : ℝ) - 2 ^ n * Real.pi| ≤ 1 :=
  bits_bound _ _ n (piApprox_bound (2 * n + 9))

theorem log2Approx_bound (M : ℕ) : |(log2Approx M : ℝ) - 2 ^ M * Real.log 2| ≤ 2 * M + 4 := by
  have h3 := atanhInv_bound 3 M M (by norm_num)
  have e3 : (2 : ℝ) * 2 ^ M / ((3 : ℕ) : ℝ) ^ (2 * M + 1) ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have := two_pow_le_pow 3 M (by norm_num); nlinarith
  have hl : (Real.log (1 + 1 / ((3 : ℕ) : ℝ)) - Real.log (1 - 1 / ((3 : ℕ) : ℝ))) / 2
      = Real.log 2 / 2 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
  rw [hl] at h3
  have hc : (log2Approx M : ℝ) = 2 * (atanhInv 3 M M : ℝ) := by unfold log2Approx; push_cast; ring
  rw [hc]
  rw [abs_le] at h3 ⊢
  constructor <;> nlinarith [h3.1, h3.2]

theorem log2Bits_bound (n : ℕ) : |(log2Bits n : ℝ) - 2 ^ n * Real.log 2| ≤ 1 := by
  refine bits_bound _ _ n ((log2Approx_bound (2 * n + 9)).trans ?_)
  have : (0 : ℝ) ≤ ((2 * n + 9 : ℕ) : ℝ) := Nat.cast_nonneg _
  linarith

end IntMul.HvdH.Num

theorem solution (n : ℕ) : |(IntMul.HvdH.log2Bits n : ℝ) - 2 ^ n * Real.log 2| ≤ 1 :=
  IntMul.HvdH.Num.log2Bits_bound n
