-- Prove2me | solution 1 for IntMul.HvdH.expPos_bound
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-11T22:22:14.201585+00:00
-- url     : https://prove2.me/submissions/d31bf327-192d-4dfe-a250-55afc83e882f

import Definitions.Def_IntMul_HvdH_RealExp
import Theorems.Thm_IntMul_HvdH_piBits_bound
import Theorems.Thm_IntMul_HvdH_log2Bits_bound
import Theorems.Thm_IntMul_HvdH_expBits_bound

open Complex

namespace IntMul.HvdH.RExpPf
open IntMul.HvdH

/-- A pair of integers as a Gaussian integer in `ℂ`. -/
def toC (p : ℤ × ℤ) : ℂ := (p.1 : ℂ) + (p.2 : ℂ) * I

@[simp] lemma toC_re (p : ℤ × ℤ) : (toC p).re = p.1 := by simp [toC]
@[simp] lemma toC_im (p : ℤ × ℤ) : (toC p).im = p.2 := by simp [toC]

lemma norm_le_of_re_im {z : ℂ} {c : ℝ} (hre : |z.re| ≤ c) (him : |z.im| ≤ c) :
    ‖z‖ ≤ 3 / 2 * c := by
  have hc : 0 ≤ c := (abs_nonneg _).trans hre
  have h1 : z.re ^ 2 ≤ c ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hre 2
  have h2 : z.im ^ 2 ≤ c ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) him 2
  have hn : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have : ‖z‖ ^ 2 ≤ (3 / 2 * c) ^ 2 := by nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).1 this

lemma int_div_err (m D : ℤ) (hD : 0 < D) :
    |(((m / D : ℤ) : ℝ)) - (m : ℝ) / D| ≤ 1 := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have h1 : (m / D) * D ≤ m := Int.ediv_mul_le _ hD.ne'
  have h2 : m < (m / D + 1) * D := Int.lt_ediv_add_one_mul_self m hD
  have h1' : ((m / D : ℤ) : ℝ) * D ≤ m := by exact_mod_cast h1
  have h2' : (m : ℝ) < ((m / D : ℤ) + 1) * D := by exact_mod_cast h2
  have e : ((m / D : ℤ) : ℝ) - (m : ℝ) / D = (((m / D : ℤ) : ℝ) * D - m) / D := by field_simp
  rw [e, abs_div, abs_of_pos hD', div_le_iff₀ hD', abs_le]
  constructor <;> nlinarith

lemma int_round_err (m : ℤ) (s : ℕ) :
    |(((m + 2 ^ s) / 2 ^ (s + 1) : ℤ) : ℝ) - (m : ℝ) / 2 ^ (s + 1)| ≤ 1 / 2 := by
  set q := (m + 2 ^ s) / 2 ^ (s + 1)
  have hd : (0 : ℤ) < 2 ^ (s + 1) := by positivity
  have h1 : q * 2 ^ (s + 1) ≤ m + 2 ^ s := Int.ediv_mul_le _ hd.ne'
  have h2 : m + 2 ^ s < (q + 1) * 2 ^ (s + 1) := by
    have := Int.lt_ediv_add_one_mul_self (m + 2 ^ s) hd; linarith
  have h1' : (q : ℝ) * 2 ^ (s + 1) ≤ m + 2 ^ s := by exact_mod_cast h1
  have h2' : (m : ℝ) + 2 ^ s < (q + 1) * 2 ^ (s + 1) := by exact_mod_cast h2
  have hp : (0 : ℝ) < 2 ^ (s + 1) := by positivity
  have hs : (2 : ℝ) ^ (s + 1) = 2 * 2 ^ s := by ring
  have e : (q : ℝ) - m / 2 ^ (s + 1) = ((q : ℝ) * 2 ^ (s + 1) - m) / 2 ^ (s + 1) := by
    field_simp
  rw [e, abs_div, abs_of_pos hp, div_le_iff₀ hp, abs_le]
  constructor <;> nlinarith

lemma lin_le_two_pow (t : ℕ) : (1 + 6 * t : ℝ) ≤ 4 * 2 ^ t := by
  induction t with
  | zero => norm_num
  | succ k ih =>
    push_cast
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · norm_num
    · have : (2 : ℝ) ≤ 2 ^ k := by
        calc (2 : ℝ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
      rw [pow_succ]; nlinarith

lemma abs_exp_sub_exp_le {a b : ℝ} (hab : |a - b| ≤ 1) (hb : b ≤ 1) :
    |Real.exp a - Real.exp b| ≤ 6 * |a - b| := by
  have e : Real.exp a - Real.exp b = Real.exp b * (Real.exp (a - b) - 1) := by
    rw [mul_sub, ← Real.exp_add]; ring_nf
  rw [e, abs_mul, abs_of_pos (Real.exp_pos b)]
  have h1 := Real.abs_exp_sub_one_le hab
  have h2 : Real.exp b ≤ 3 := by
    calc Real.exp b ≤ Real.exp 1 := Real.exp_le_exp.2 hb
      _ ≤ 3 := by have := Real.exp_one_lt_d9; norm_num at this; linarith
  calc Real.exp b * |Real.exp (a - b) - 1| ≤ 3 * (2 * |a - b|) :=
        mul_le_mul h2 h1 (abs_nonneg _) (by norm_num)
    _ = 6 * |a - b| := by ring

/-- Real part of `expBits` for a real argument. -/
lemma expBits_real (M : ℕ) (Z : ℤ) (h : |(Z : ℝ)| ≤ 2 ^ M) :
    |((expBits M Z 0).1 : ℝ) - 2 ^ M * Real.exp (Z / 2 ^ M)| ≤ 1 := by
  have hin : ‖(Z : ℂ) + ((0 : ℤ) : ℂ) * I‖ ≤ 2 ^ M := by
    simp only [Int.cast_zero, zero_mul, add_zero]
    rw [show ((Z : ℂ)) = ((Z : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real, Real.norm_eq_abs]
    exact h
  have hb := expBits_bound M Z 0 hin
  have e : ((Z : ℂ) + ((0 : ℤ) : ℂ) * I) / 2 ^ M = (((Z : ℝ) / 2 ^ M : ℝ) : ℂ) := by
    push_cast; ring
  have key : (2 : ℂ) ^ M * cexp (((Z : ℂ) + ((0 : ℤ) : ℂ) * I) / 2 ^ M)
      = (((2 : ℝ) ^ M * Real.exp ((Z : ℝ) / 2 ^ M) : ℝ) : ℂ) := by
    rw [e, Complex.ofReal_mul, Complex.ofReal_exp]; push_cast; rfl
  rw [key] at hb
  have := (Complex.abs_re_le_norm _).trans hb
  rw [Complex.sub_re, Complex.ofReal_re] at this
  simpa using this

theorem expNegFix_bound (n M : ℕ) (hM : n + 10 ≤ M) (X : ℤ) (hX : X ≤ 0)
    (hXb : 16 * (-(X : ℝ)) ≤ 2 ^ M * 2 ^ M) :
    |(expNegFix n M X : ℝ) - 2 ^ n * Real.exp (X / 2 ^ M)| ≤ 3 / 4 := by
  set L : ℤ := log2Bits M with hLdef
  have hL : |(L : ℝ) - 2 ^ M * Real.log 2| ≤ 1 := log2Bits_bound M
  have h2M : (1024 : ℝ) ≤ 2 ^ M := by
    have : (2 : ℝ) ^ 10 ≤ 2 ^ M := pow_le_pow_right₀ (by norm_num) (by omega)
    norm_num at this; exact this
  have hl1 := Real.log_two_gt_d9
  have hl2 := Real.log_two_lt_d9
  rw [abs_le] at hL
  have hLlo : (0.6 : ℝ) * 2 ^ M ≤ L := by nlinarith
  have hLhi : (L : ℝ) ≤ 0.7 * 2 ^ M := by nlinarith
  have hLpos : 0 < L := by
    have : (0 : ℝ) < L := by nlinarith
    exact_mod_cast this
  set τ : ℤ := (-X) / L with hτdef
  have hτ0 : 0 ≤ τ := Int.ediv_nonneg (by omega) hLpos.le
  have hτ1 : τ * L ≤ -X := Int.ediv_mul_le _ hLpos.ne'
  have hτ2 : -X < (τ + 1) * L := Int.lt_ediv_add_one_mul_self _ hLpos
  set Z : ℤ := X + τ * L with hZdef
  have hZ1 : -L < Z := by rw [hZdef]; linarith
  have hZ2 : Z ≤ 0 := by rw [hZdef]; linarith
  have hZr : |(Z : ℝ)| ≤ 2 ^ M := by
    have a1 : (-(L : ℝ)) < Z := by exact_mod_cast hZ1
    have a2 : (Z : ℝ) ≤ 0 := by exact_mod_cast hZ2
    rw [abs_le]; constructor <;> nlinarith
  have hu := expBits_real M Z hZr
  set u : ℤ := (expBits M Z 0).1
  set t : ℕ := τ.toNat
  have ht : (t : ℤ) = τ := Int.toNat_of_nonneg hτ0
  have htR : (t : ℝ) = (τ : ℝ) := by exact_mod_cast ht
  -- τ is small compared with 2^M
  have hτ1R : (τ : ℝ) * L ≤ -(X : ℝ) := by exact_mod_cast hτ1
  have hτ0R : (0 : ℝ) ≤ τ := by exact_mod_cast hτ0
  have hp : (0 : ℝ) < 2 ^ M := by positivity
  have hδ : (τ : ℝ) / 2 ^ M ≤ 1 / 9 := by
    rw [div_le_iff₀ hp]
    have : (τ : ℝ) * (0.6 * 2 ^ M) ≤ 2 ^ M * 2 ^ M / 16 := by nlinarith
    nlinarith
  set z : ℝ := X / 2 ^ M + t * Real.log 2 with hzdef
  have hZz : |(Z : ℝ) / 2 ^ M - z| ≤ (τ : ℝ) / 2 ^ M := by
    have e : (Z : ℝ) / 2 ^ M - z = (τ : ℝ) * ((L : ℝ) - 2 ^ M * Real.log 2) / 2 ^ M := by
      rw [hzdef, htR, hZdef]; push_cast; field_simp; ring
    rw [e, abs_div, abs_mul, abs_of_nonneg hτ0R, abs_of_pos hp]
    apply div_le_div_of_nonneg_right _ hp.le
    have : |(L : ℝ) - 2 ^ M * Real.log 2| ≤ 1 := abs_le.2 hL
    nlinarith [abs_nonneg ((L : ℝ) - 2 ^ M * Real.log 2)]
  have hz1 : z ≤ 1 := by
    have : (Z : ℝ) / 2 ^ M ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hZ2) hp.le
    rw [abs_le] at hZz; linarith
  have hez : |Real.exp ((Z : ℝ) / 2 ^ M) - Real.exp z| ≤ 6 * ((τ : ℝ) / 2 ^ M) :=
    (abs_exp_sub_exp_le (hZz.trans (by linarith)) hz1).trans (by linarith)
  have hu2 : |(u : ℝ) - 2 ^ M * Real.exp z| ≤ 1 + 6 * t := by
    have e : (u : ℝ) - 2 ^ M * Real.exp z = ((u : ℝ) - 2 ^ M * Real.exp ((Z : ℝ) / 2 ^ M))
        + 2 ^ M * (Real.exp ((Z : ℝ) / 2 ^ M) - Real.exp z) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_pos hp]
    have : 2 ^ M * |Real.exp ((Z : ℝ) / 2 ^ M) - Real.exp z| ≤ 6 * τ := by
      have := mul_le_mul_of_nonneg_left hez hp.le
      rwa [show (2 : ℝ) ^ M * (6 * ((τ : ℝ) / 2 ^ M)) = 6 * τ by field_simp] at this
    rw [htR]; linarith
  -- rounding
  set s : ℕ := M - n - 1 + t
  have hs1 : s + 1 = (M - n) + t := by omega
  have hres : expNegFix n M X = (u + 2 ^ s) / 2 ^ (s + 1) := rfl
  rw [hres]
  have hr := int_round_err u s
  have hps : (0 : ℝ) < 2 ^ (s + 1) := by positivity
  have hkey : (2 : ℝ) ^ n * Real.exp (X / 2 ^ M) = 2 ^ M * Real.exp z / 2 ^ (s + 1) := by
    rw [hs1, hzdef, Real.exp_add, Real.exp_nat_mul, Real.exp_log two_pos,
      pow_add]
    have : (2 : ℝ) ^ M = 2 ^ (M - n) * 2 ^ n := by rw [← pow_add]; congr 1; omega
    rw [this]; field_simp
  have hmn : (1024 : ℝ) ≤ 2 ^ (M - n) := by
    have : (2 : ℝ) ^ 10 ≤ 2 ^ (M - n) := pow_le_pow_right₀ (by norm_num) (by omega)
    norm_num at this; exact this
  have hq : |(u : ℝ) / 2 ^ (s + 1) - 2 ^ n * Real.exp (X / 2 ^ M)| ≤ 1 / 4 := by
    rw [hkey, ← sub_div, abs_div, abs_of_pos hps, div_le_iff₀ hps]
    refine hu2.trans ?_
    have hl := lin_le_two_pow t
    rw [hs1, pow_add]
    have : (0 : ℝ) < 2 ^ t := by positivity
    nlinarith
  calc |(((u + 2 ^ s) / 2 ^ (s + 1) : ℤ) : ℝ) - 2 ^ n * Real.exp (X / 2 ^ M)|
      ≤ |(((u + 2 ^ s) / 2 ^ (s + 1) : ℤ) : ℝ) - u / 2 ^ (s + 1)|
        + |(u : ℝ) / 2 ^ (s + 1) - 2 ^ n * Real.exp (X / 2 ^ M)| := abs_sub_le _ _ _
    _ ≤ 3 / 4 := by linarith

lemma exp_lip_nonpos {a b : ℝ} (ha : a ≤ 0) (hb : b ≤ 0) :
    |Real.exp a - Real.exp b| ≤ |a - b| := by
  have key : ∀ x y : ℝ, x ≤ y → y ≤ 0 → Real.exp y - Real.exp x ≤ y - x := by
    intro x y hxy hy
    have h1 := Real.add_one_le_exp (x - y)
    have h2 : Real.exp x = Real.exp y * Real.exp (x - y) := by rw [← Real.exp_add]; ring_nf
    have h3 : Real.exp y ≤ 1 := Real.exp_le_one_iff.2 hy
    have h4 := Real.exp_pos y
    rw [h2]; nlinarith
  rcases le_total a b with h | h
  · have := key a b h hb
    have : Real.exp a ≤ Real.exp b := Real.exp_le_exp.2 h
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
  · have := key b a h ha
    have : Real.exp b ≤ Real.exp a := Real.exp_le_exp.2 h
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith

lemma pow_lin (n : ℕ) (c : ℝ) (hc : c ≤ 64) : c * (n + 1) ≤ 2 ^ (n + 10) / 4 := by
  have h : (n + 1 : ℝ) ≤ 2 ^ n := by
    have := Nat.lt_two_pow_self (n := n)
    have : ((n + 1 : ℕ) : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at this; exact this
  have : (2 : ℝ) ^ (n + 10) = 1024 * 2 ^ n := by ring
  rw [this]
  have hn : (0 : ℝ) ≤ n + 1 := by positivity
  rcases le_total c 0 with hc0 | hc0
  · have : c * (n + 1) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc0 hn
    have : (0 : ℝ) ≤ 1024 * 2 ^ n / 4 := by positivity
    linarith
  · nlinarith

/-- Generic corollary: an approximation `X` of `2^M x` (`x ≤ 0`) with error `D` gives
`2^n e^x` with error `3/4 + D / 2^{n+10}`. -/
lemma expNegFix_approx (n : ℕ) (X : ℤ) (x D : ℝ) (hX : X ≤ 0) (hx : x ≤ 0)
    (hXb : 16 * (-(X : ℝ)) ≤ 2 ^ (2 * n + 10) * 2 ^ (2 * n + 10))
    (hD : |(X : ℝ) - 2 ^ (2 * n + 10) * x| ≤ D) :
    |(expNegFix n (2 * n + 10) X : ℝ) - 2 ^ n * Real.exp x| ≤ 3 / 4 + D / 2 ^ (n + 10) := by
  have h1 := expNegFix_bound n (2 * n + 10) (by omega) X hX hXb
  have hp : (0 : ℝ) < 2 ^ (2 * n + 10) := by positivity
  have hXM : (X : ℝ) / 2 ^ (2 * n + 10) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hX) hp.le
  have h2 := exp_lip_nonpos hXM hx
  have e : (X : ℝ) / 2 ^ (2 * n + 10) - x = ((X : ℝ) - 2 ^ (2 * n + 10) * x) / 2 ^ (2 * n + 10) := by
    field_simp
  rw [e, abs_div, abs_of_pos hp] at h2
  have h3 : 2 ^ n * |Real.exp ((X : ℝ) / 2 ^ (2 * n + 10)) - Real.exp x| ≤ D / 2 ^ (n + 10) := by
    have hpn : (0 : ℝ) < 2 ^ n := by positivity
    have : (2 : ℝ) ^ (2 * n + 10) = 2 ^ n * 2 ^ (n + 10) := by rw [← pow_add]; congr 1; omega
    calc 2 ^ n * |Real.exp ((X : ℝ) / 2 ^ (2 * n + 10)) - Real.exp x|
        ≤ 2 ^ n * (|(X : ℝ) - 2 ^ (2 * n + 10) * x| / 2 ^ (2 * n + 10)) :=
          mul_le_mul_of_nonneg_left h2 hpn.le
      _ = |(X : ℝ) - 2 ^ (2 * n + 10) * x| / 2 ^ (n + 10) := by rw [this]; field_simp
      _ ≤ D / 2 ^ (n + 10) := div_le_div_of_nonneg_right hD (by positivity)
  have e2 : (expNegFix n (2 * n + 10) X : ℝ) - 2 ^ n * Real.exp x =
      ((expNegFix n (2 * n + 10) X : ℝ) - 2 ^ n * Real.exp (X / 2 ^ (2 * n + 10)))
        + 2 ^ n * (Real.exp ((X : ℝ) / 2 ^ (2 * n + 10)) - Real.exp x) := by ring
  rw [e2]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ n)]
  linarith

theorem expNeg_bound (n k j : ℕ) (hk : 0 < k) :
    |(expNeg n k j : ℝ) - 2 ^ n * Real.exp (-(Real.pi * j / k))| ≤ 1 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hpi := Real.pi_gt_three
  have hpi2 := Real.pi_lt_d2
  unfold expNeg
  split_ifs with hj
  · -- tiny case
    have hjR : (k : ℝ) * n < j := by exact_mod_cast hj
    have h1 : (n : ℝ) * Real.log 2 ≤ Real.pi * j / k := by
      rw [le_div_iff₀ hkR]
      have := Real.log_two_lt_d9
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have a : (n : ℝ) * k * Real.log 2 ≤ n * k * Real.pi :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have b : (n : ℝ) * k * Real.pi ≤ j * Real.pi :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      linarith
    have h2 : Real.exp (-(Real.pi * j / k)) ≤ Real.exp (-(n * Real.log 2)) :=
      Real.exp_le_exp.2 (by linarith)
    have h3 : Real.exp (-(n * Real.log 2)) * 2 ^ n = 1 := by
      rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log two_pos]
      field_simp
    have h4 : 0 < Real.exp (-(Real.pi * j / k)) := Real.exp_pos _
    rw [Int.cast_zero, zero_sub, abs_neg, abs_of_pos (by positivity)]
    nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) n]
  · push Not at hj
    have hjR : (j : ℝ) ≤ k * n := by exact_mod_cast hj
    have hjk : (j : ℝ) / k ≤ n := by rw [div_le_iff₀ hkR]; linarith
    have hj0 : (0 : ℝ) ≤ j / k := by positivity
    set M := 2 * n + 10
    set P : ℤ := piBits M
    have hP : |(P : ℝ) - 2 ^ M * Real.pi| ≤ 1 := piBits_bound M
    have hp : (0 : ℝ) < 2 ^ M := by positivity
    have hPpos : (0 : ℝ) ≤ P := by
      have h1M : (1 : ℝ) ≤ 2 ^ M := one_le_pow₀ (by norm_num)
      rw [abs_le] at hP; nlinarith
    have hD : (0 : ℤ) < k := by exact_mod_cast hk
    have hf := int_div_err (P * j) k hD
    have hfl : (0 : ℤ) ≤ P * j / k := by
      apply Int.ediv_nonneg _ hD.le
      have : (0 : ℤ) ≤ P := by exact_mod_cast hPpos
      positivity
    have e1 : ((P * j : ℤ) : ℝ) / ((k : ℤ) : ℝ) - 2 ^ M * (Real.pi * j / k)
        = ((P : ℝ) - 2 ^ M * Real.pi) * (j / k) := by push_cast; field_simp
    have hD2 : |((-(P * j / k) : ℤ) : ℝ) - 2 ^ M * (-(Real.pi * j / k))| ≤ n + 1 := by
      have : ((-(P * j / k) : ℤ) : ℝ) - 2 ^ M * (-(Real.pi * j / k))
          = -((((P * j / k : ℤ) : ℝ) - ((P * j : ℤ) : ℝ) / ((k : ℤ) : ℝ))
            + (((P * j : ℤ) : ℝ) / ((k : ℤ) : ℝ) - 2 ^ M * (Real.pi * j / k))) := by
        push_cast; ring
      rw [this, abs_neg, e1]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_nonneg hj0]
      have : |(P : ℝ) - 2 ^ M * Real.pi| * (j / k) ≤ 1 * n :=
        mul_le_mul hP hjk hj0 (by norm_num)
      linarith
    have hXb : 16 * (-(((-(P * j / k) : ℤ)) : ℝ)) ≤ 2 ^ M * 2 ^ M := by
      have hfl' : (((P * j / k : ℤ)) : ℝ) ≤ 2 ^ M * (Real.pi * j / k) + (n + 1) := by
        have := abs_le.1 hD2; push_cast at this ⊢; linarith
      push_cast
      have h64 : (64 : ℝ) * (n + 1) ≤ 2 ^ M := by
        have := pow_lin n 64 le_rfl
        have h2 : (2 : ℝ) ^ (n + 10) ≤ 2 ^ M := pow_le_pow_right₀ (by norm_num) (by omega)
        linarith
      have h1M : (1 : ℝ) ≤ 2 ^ M := one_le_pow₀ (by norm_num)
      have : Real.pi * j / k ≤ 4 * n := by
        rw [mul_div_assoc]; nlinarith
      nlinarith
    have hX0 : (-(P * j / k) : ℤ) ≤ 0 := by omega
    have hx0 : -(Real.pi * j / k) ≤ 0 := by
      have : 0 ≤ Real.pi * j / k := by positivity
      linarith
    have := expNegFix_approx n (-(P * j / k)) _ _ hX0 hx0 hXb hD2
    have hsmall : ((n : ℝ) + 1) / 2 ^ (n + 10) ≤ 1 / 4 := by
      rw [div_le_iff₀ (by positivity)]
      have := pow_lin n 1 (by norm_num); linarith
    linarith

theorem expPos_bound (n k j σ : ℕ) (hk : 0 < k) (hσ : Real.exp (Real.pi * j / k) ≤ 2 ^ σ)
    (hσn : σ ≤ 2 * n) :
    |(expPos n k j σ : ℝ) - 2 ^ n * ((2 ^ σ)⁻¹ * Real.exp (Real.pi * j / k))| ≤ 1 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hpi := Real.pi_gt_three
  have hl1 := Real.log_two_gt_d9
  have hl2 := Real.log_two_lt_d9
  set M := 2 * n + 10
  set x : ℝ := Real.pi * j / k - σ * Real.log 2 with hxdef
  have hlog : Real.pi * j / k ≤ σ * Real.log 2 := by
    have := Real.log_le_log (Real.exp_pos _) hσ
    rwa [Real.log_exp, Real.log_pow] at this
  have hx : x ≤ 0 := by rw [hxdef]; linarith
  have hex : (2 ^ σ : ℝ)⁻¹ * Real.exp (Real.pi * j / k) = Real.exp x := by
    rw [hxdef, Real.exp_sub, Real.exp_nat_mul, Real.exp_log two_pos]
    field_simp
  rw [hex]
  have hjk : (j : ℝ) / k ≤ 2 * n := by
    have h1 : Real.pi * (j / k) ≤ σ * Real.log 2 := by rw [← mul_div_assoc]; exact hlog
    have hσR : (σ : ℝ) ≤ 2 * n := by exact_mod_cast hσn
    have hj0 : (0 : ℝ) ≤ j / k := by positivity
    nlinarith
  have hj0 : (0 : ℝ) ≤ j / k := by positivity
  set P : ℤ := piBits M
  set L : ℤ := log2Bits M
  have hP : |(P : ℝ) - 2 ^ M * Real.pi| ≤ 1 := piBits_bound M
  have hL : |(L : ℝ) - 2 ^ M * Real.log 2| ≤ 1 := log2Bits_bound M
  have hD : (0 : ℤ) < k := by exact_mod_cast hk
  have hf := int_div_err (P * j) k hD
  set X0 : ℤ := P * j / k - σ * L
  have e1 : ((P * j : ℤ) : ℝ) / ((k : ℤ) : ℝ) - 2 ^ M * (Real.pi * j / k)
      = ((P : ℝ) - 2 ^ M * Real.pi) * (j / k) := by push_cast; field_simp
  have hσR : (σ : ℝ) ≤ 2 * n := by exact_mod_cast hσn
  have hD0 : |(X0 : ℝ) - 2 ^ M * x| ≤ 4 * n + 1 := by
    have : (X0 : ℝ) - 2 ^ M * x
        = (((P * j / k : ℤ) : ℝ) - ((P * j : ℤ) : ℝ) / ((k : ℤ) : ℝ))
          + (((P * j : ℤ) : ℝ) / ((k : ℤ) : ℝ) - 2 ^ M * (Real.pi * j / k))
          - σ * ((L : ℝ) - 2 ^ M * Real.log 2) := by
      simp only [X0, hxdef]; push_cast; ring
    rw [this, e1]
    have a1 : |((P : ℝ) - 2 ^ M * Real.pi) * (j / k)| ≤ 2 * n := by
      rw [abs_mul, abs_of_nonneg hj0]
      exact (mul_le_mul hP hjk hj0 (by norm_num)).trans (by linarith)
    have a2 : |(σ : ℝ) * ((L : ℝ) - 2 ^ M * Real.log 2)| ≤ 2 * n := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg σ)]
      exact (mul_le_mul hσR hL (abs_nonneg _) (by positivity)).trans (by linarith)
    have := abs_sub (((P * j / k : ℤ) : ℝ) - ((P * j : ℤ) : ℝ) / ((k : ℤ) : ℝ)
      + ((P : ℝ) - 2 ^ M * Real.pi) * (j / k)) ((σ : ℝ) * ((L : ℝ) - 2 ^ M * Real.log 2))
    have := abs_add_le (((P * j / k : ℤ) : ℝ) - ((P * j : ℤ) : ℝ) / ((k : ℤ) : ℝ))
      (((P : ℝ) - 2 ^ M * Real.pi) * (j / k))
    linarith
  have hp : (0 : ℝ) < 2 ^ M := by positivity
  have hMx : 2 ^ M * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hp.le hx
  have hD1 : |((min 0 X0 : ℤ) : ℝ) - 2 ^ M * x| ≤ 4 * n + 1 := by
    rcases le_total 0 X0 with h | h
    · rw [min_eq_left h]; push_cast
      have : (0 : ℝ) ≤ X0 := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]
      have := (abs_le.1 hD0).2; linarith
    · rw [min_eq_right h]; exact hD0
  have hX0 : min 0 X0 ≤ 0 := min_le_left _ _
  have hXb : 16 * (-(((min 0 X0 : ℤ)) : ℝ)) ≤ 2 ^ M * 2 ^ M := by
    have a := (abs_le.1 hD1).1
    have hxlo : -(σ * Real.log 2) ≤ x := by
      have : 0 ≤ Real.pi * j / k := by positivity
      rw [hxdef]; linarith
    have h64 : (64 : ℝ) * (n + 1) ≤ 2 ^ M := by
      have := pow_lin n 64 le_rfl
      have h2 : (2 : ℝ) ^ (n + 10) ≤ 2 ^ M := pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
    have h1M : (1 : ℝ) ≤ 2 ^ M := one_le_pow₀ (by norm_num)
    have : -x ≤ 2 * n := by nlinarith
    nlinarith
  have := expNegFix_approx n (min 0 X0) x _ hX0 hx hXb hD1
  have hsmall : (4 * (n : ℝ) + 1) / 2 ^ (n + 10) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity)]
    have := pow_lin n 4 (by norm_num); nlinarith
  have hdef : expPos n k j σ = expNegFix n M (min 0 X0) := rfl
  rw [hdef]
  linarith

end IntMul.HvdH.RExpPf

open IntMul.HvdH in
theorem solution (n k j σ : ℕ) (hk : 0 < k) (hσ : Real.exp (Real.pi * j / k) ≤ 2 ^ σ)
    (hσn : σ ≤ 2 * n) :
    |(expPos n k j σ : ℝ) - 2 ^ n * ((2 ^ σ)⁻¹ * Real.exp (Real.pi * j / k))| ≤ 1 :=
  IntMul.HvdH.RExpPf.expPos_bound n k j σ hk hσ hσn
