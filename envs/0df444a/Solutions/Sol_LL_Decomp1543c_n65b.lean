-- Prove2me | solution 1 for LL_Decomp1543c.n65b
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T10:05:33.135041+00:00
-- url     : https://prove2.me/submissions/29541b00-17da-455f-a128-913d64697865

import Mathlib
import Definitions.Def_LL_Decomp1543c_Vf

open Real Finset ArithmeticFunction

namespace VaBAux
open Real

lemma q_facts {N q : ℝ} (hN : 0 < N) (hL : 3100 ≤ Real.log N)
    (hq1 : (0.28 / 1.0012) ^ 2 * Real.log N ^ 4 < q)
    (hq2 : q < (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5) :
    1 ≤ q ∧ q ≤ N ∧ 0 ≤ Real.log q ∧ Real.log q ≤ Real.log N := by
  have hL0 : 0 < Real.log N := by linarith
  have hL4 : (3100:ℝ) ^ 4 ≤ Real.log N ^ 4 := pow_le_pow_left₀ (by norm_num) hL 4
  have hL5 : (3100:ℝ) ^ 5 ≤ Real.log N ^ 5 := pow_le_pow_left₀ (by norm_num) hL 5
  have h1 : 1 ≤ q := by
    have := mul_le_mul_of_nonneg_left hL4 (by positivity : (0:ℝ) ≤ (0.28 / 1.0012) ^ 2)
    have h : (1:ℝ) ≤ (0.28 / 1.0012) ^ 2 * 3100 ^ 4 := by norm_num
    linarith
  have h2 : q ≤ N := by
    have hc : (1.0012 / 0.09) ^ 2 ≤ Real.log N ^ 5 := by
      have : (1.0012 / 0.09 : ℝ) ^ 2 ≤ 3100 ^ 5 := by norm_num
      linarith
    have : (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5 ≤ N := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hc hN.le]
    linarith
  refine ⟨h1, h2, Real.log_nonneg h1, Real.log_le_log (by linarith) h2⟩

lemma sqrtq_lb {N q : ℝ} (hL : 3100 ≤ Real.log N)
    (hq1 : (0.28 / 1.0012) ^ 2 * Real.log N ^ 4 < q) :
    (0.28 / 1.0012) * Real.log N ^ 2 ≤ √q := by
  have hL0 : 0 < Real.log N := by linarith
  calc (0.28 / 1.0012) * Real.log N ^ 2 = √(((0.28 / 1.0012) * Real.log N ^ 2) ^ 2) :=
        (Real.sqrt_sq (by positivity)).symm
    _ ≤ √q := Real.sqrt_le_sqrt (by nlinarith)

lemma sqrtq_ub {N q : ℝ} (hN : 0 < N) (hq0 : 0 ≤ q) (hL : 3100 ≤ Real.log N)
    (hq2 : q < (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5) :
    √q * (√(Real.log N)) ^ 5 ≤ 11.14 * √N := by
  have hL0 : 0 < Real.log N := by linarith
  have hsq : (√(Real.log N)) ^ 2 = Real.log N := Real.sq_sqrt hL0.le
  have h5 : q * Real.log N ^ 5 ≤ (1.0012 / 0.09) ^ 2 * N := by
    have := (lt_div_iff₀ (by positivity : (0:ℝ) < Real.log N ^ 5)).1 hq2
    linarith
  have hN2 : (√N) ^ 2 = N := Real.sq_sqrt hN.le
  have hsq' : (√q) ^ 2 = q := Real.sq_sqrt hq0
  have hle : (√q * (√(Real.log N)) ^ 5) ^ 2 ≤ (11.14 * √N) ^ 2 := by
    have : (√q * (√(Real.log N)) ^ 5) ^ 2 = q * Real.log N ^ 5 := by
      rw [mul_pow, hsq', ← pow_mul, mul_comm 5 2, pow_mul, hsq]
    rw [this, mul_pow, hN2]
    nlinarith
  exact le_of_sq_le_sq hle (by positivity)


lemma N_big {N : ℝ} (hN : 0 < N) (hL : 3100 ≤ Real.log N) :
    10000 * Real.log N ≤ N ^ ((2:ℝ) / 5) := by
  have hL0 : 0 < Real.log N := by linarith
  rw [Real.rpow_def_of_pos hN]
  have h := Real.pow_div_factorial_le_exp (0.4 * Real.log N) (by positivity) 3
  have e : Real.log N * ((2:ℝ) / 5) = 0.4 * Real.log N := by ring
  rw [e]
  refine le_trans ?_ h
  rw [Nat.factorial]
  norm_num
  nlinarith [mul_pos hL0 hL0]

lemma s_le_pt {N q : ℝ} (hN : 0 < N) (hq0 : 0 ≤ q) (hL : 3100 ≤ Real.log N)
    (hq2 : q < (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5) :
    √q ≤ 0.0003 * √N * √(Real.log N) := by
  have hL0 : 0 < Real.log N := by linarith
  have hub := sqrtq_ub hN hq0 hL hq2
  have ht : 0 < √(Real.log N) := Real.sqrt_pos.2 hL0
  have hp : 0 < √N := Real.sqrt_pos.2 hN
  have hsq : (√(Real.log N)) ^ 2 = Real.log N := Real.sq_sqrt hL0.le
  have h6 : (3100:ℝ) ^ 3 ≤ (√(Real.log N)) ^ 6 := by
    have : (√(Real.log N)) ^ 6 = Real.log N ^ 3 := by
      rw [show (6:ℕ) = 2 * 3 from rfl, pow_mul, hsq]
    rw [this]
    exact pow_le_pow_left₀ (by norm_num) hL 3
  have h5 : 0 < (√(Real.log N)) ^ 5 := by positivity
  refine le_of_mul_le_mul_right ?_ h5
  have : 0.0003 * √N * √(Real.log N) * (√(Real.log N)) ^ 5 = 0.0003 * √N * (√(Real.log N)) ^ 6 := by
    ring
  rw [this]
  nlinarith [mul_le_mul_of_nonneg_left h6 (by positivity : (0:ℝ) ≤ 0.0003 * √N)]

lemma rpow_25 {L : ℝ} (hL0 : 0 < L) : L ^ ((2.5 : ℝ)) = (√L) ^ 5 := by
  rw [show (2.5:ℝ) = (1/2) * ((5:ℕ):ℝ) by norm_num, Real.rpow_mul hL0.le, Real.rpow_natCast,
    ← Real.sqrt_eq_rpow]

lemma core_n65a {N q : ℝ} (hN : 0 < N) (hL : 3100 ≤ Real.log N)
    (hq1 : (0.28 / 1.0012) ^ 2 * Real.log N ^ 4 < q)
    (hq2 : q < (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5) :
    (5 * q + 1.5 * q * Real.log q) * Real.log N ≤
      0.0006 * √N * √q * Real.log N ^ (2.5 : ℝ) := by
  obtain ⟨h1, h2, h3, h4⟩ := q_facts hN hL hq1 hq2
  have hL0 : 0 < Real.log N := by linarith
  have hq0 : 0 ≤ q := by linarith
  have hs := s_le_pt hN hq0 hL hq2
  rw [rpow_25 hL0]
  have ht : 0 < √(Real.log N) := Real.sqrt_pos.2 hL0
  have hsq : (√(Real.log N)) ^ 2 = Real.log N := Real.sq_sqrt hL0.le
  have e4 : (√(Real.log N)) ^ 4 = Real.log N ^ 2 := by
    rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, hsq]
  have hs0 : 0 ≤ √q := Real.sqrt_nonneg _
  have hA : (5 * q + 1.5 * q * Real.log q) ≤ 2 * Real.log N * q := by
    nlinarith [mul_le_mul_of_nonneg_left h4 hq0]
  calc (5 * q + 1.5 * q * Real.log q) * Real.log N ≤ 2 * Real.log N * q * Real.log N :=
        mul_le_mul_of_nonneg_right hA hL0.le
    _ = (2 * (√(Real.log N)) ^ 4 * √q) * √q := by
        rw [e4, show 2 * Real.log N ^ 2 * √q * √q = 2 * Real.log N ^ 2 * (√q * √q) by ring,
          Real.mul_self_sqrt hq0]; ring
    _ ≤ (2 * (√(Real.log N)) ^ 4 * √q) * (0.0003 * √N * √(Real.log N)) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
    _ = 0.0006 * √N * √q * (√(Real.log N)) ^ 5 := by ring

lemma UV_eq {N L : ℝ} (hN : 0 < N) (hL0 : 0 < L) :
    N ^ ((2:ℝ) / 5) * L ^ (-(4:ℝ) / 5) * (N ^ ((2:ℝ) / 5) * L ^ ((1:ℝ) / 5)) =
      N ^ ((4:ℝ) / 5) * L ^ (-(3:ℝ) / 5) := by
  have : N ^ ((2:ℝ) / 5) * L ^ (-(4:ℝ) / 5) * (N ^ ((2:ℝ) / 5) * L ^ ((1:ℝ) / 5)) =
      (N ^ ((2:ℝ) / 5) * N ^ ((2:ℝ) / 5)) * (L ^ (-(4:ℝ) / 5) * L ^ ((1:ℝ) / 5)) := by ring
  rw [this, ← Real.rpow_add hN, ← Real.rpow_add hL0]
  norm_num

lemma logUV {N : ℝ} (hN : 0 < N) (hL : 3100 ≤ Real.log N) :
    0 ≤ Real.log (N ^ ((4:ℝ) / 5) * Real.log N ^ (-(3:ℝ) / 5)) ∧
    Real.log (N ^ ((4:ℝ) / 5) * Real.log N ^ (-(3:ℝ) / 5)) ≤ 0.8 * Real.log N := by
  have hL0 : 0 < Real.log N := by linarith
  rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hN, Real.log_rpow hL0]
  have h1 := Real.log_le_sub_one_of_pos hL0
  have h2 : 0 ≤ Real.log (Real.log N) := Real.log_nonneg (by linarith)
  constructor <;> nlinarith

lemma logV {N : ℝ} (hN : 0 < N) (hL : 3100 ≤ Real.log N) :
    Real.log (N ^ ((2:ℝ) / 5) * Real.log N ^ ((1:ℝ) / 5)) ≤ 0.6 * Real.log N := by
  have hL0 : 0 < Real.log N := by linarith
  rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hN, Real.log_rpow hL0]
  have h1 := Real.log_le_sub_one_of_pos hL0
  nlinarith

lemma core_n66a {N q : ℝ} (hN : 0 < N) (hL : 3100 ≤ Real.log N)
    (hq1 : (0.28 / 1.0012) ^ 2 * Real.log N ^ 4 < q)
    (hq2 : q < (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5) :
    (5 * q + 1.5 * q * Real.log q) *
      Real.log (N ^ ((2:ℝ) / 5) * Real.log N ^ (-(4:ℝ) / 5) *
        (N ^ ((2:ℝ) / 5) * Real.log N ^ ((1:ℝ) / 5))) ≤
      0.0005 * √N * √q * Real.log N ^ (2.5 : ℝ) := by
  obtain ⟨h1, h2, h3, h4⟩ := q_facts hN hL hq1 hq2
  have hL0 : 0 < Real.log N := by linarith
  have hq0 : 0 ≤ q := by linarith
  have hs := s_le_pt hN hq0 hL hq2
  rw [rpow_25 hL0, UV_eq hN hL0]
  obtain ⟨hY0, hY1⟩ := logUV hN hL
  have ht : 0 < √(Real.log N) := Real.sqrt_pos.2 hL0
  have hsq : (√(Real.log N)) ^ 2 = Real.log N := Real.sq_sqrt hL0.le
  have e4 : (√(Real.log N)) ^ 4 = Real.log N ^ 2 := by
    rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, hsq]
  have hs0 : 0 ≤ √q := Real.sqrt_nonneg _
  have hp0 : 0 ≤ √N := Real.sqrt_nonneg _
  have hA : (5 * q + 1.5 * q * Real.log q) ≤ 2 * Real.log N * q := by
    nlinarith [mul_le_mul_of_nonneg_left h4 hq0]
  calc (5 * q + 1.5 * q * Real.log q) * Real.log (N ^ ((4:ℝ) / 5) * Real.log N ^ (-(3:ℝ) / 5))
      ≤ (2 * Real.log N * q) * (0.8 * Real.log N) :=
        mul_le_mul hA hY1 hY0 (by positivity)
    _ = (1.6 * (√(Real.log N)) ^ 4 * √q) * √q := by
        rw [e4, show 1.6 * Real.log N ^ 2 * √q * √q = 1.6 * Real.log N ^ 2 * (√q * √q) by ring,
          Real.mul_self_sqrt hq0]; ring
    _ ≤ (1.6 * (√(Real.log N)) ^ 4 * √q) * (0.0003 * √N * √(Real.log N)) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
    _ = 0.00048 * (√N * √q * (√(Real.log N)) ^ 5) := by ring
    _ ≤ 0.0005 * √N * √q * (√(Real.log N)) ^ 5 := by
        have : 0 ≤ √N * √q * (√(Real.log N)) ^ 5 := by positivity
        nlinarith

lemma core_n65b {N q : ℝ} (hN : 0 < N) (hL : 3100 ≤ Real.log N)
    (hq1 : (0.28 / 1.0012) ^ 2 * Real.log N ^ 4 < q)
    (hq2 : q < (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5) :
    (N ^ ((2:ℝ) / 5) * Real.log N ^ ((1:ℝ) / 5)) * Real.log q * Real.log N ≤
      0.0001 * N ^ ((4:ℝ) / 5) * Real.log N ^ (1.4 : ℝ) := by
  obtain ⟨h1, h2, h3, h4⟩ := q_facts hN hL hq1 hq2
  have hL0 : 0 < Real.log N := by linarith
  have hA := N_big hN hL
  have hN45 : N ^ ((4:ℝ) / 5) = N ^ ((2:ℝ) / 5) * N ^ ((2:ℝ) / 5) := by
    rw [← Real.rpow_add hN]; norm_num
  have hL14 : Real.log N ^ (1.4 : ℝ) =
      Real.log N ^ ((1:ℝ) / 5) * Real.log N ^ ((6:ℝ) / 5) := by
    rw [← Real.rpow_add hL0]; norm_num
  have hC : Real.log N ≤ Real.log N ^ ((6:ℝ) / 5) := by
    calc Real.log N = Real.log N ^ (1:ℝ) := (Real.rpow_one _).symm
      _ ≤ Real.log N ^ ((6:ℝ) / 5) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  rw [hN45, hL14]
  set A := N ^ ((2:ℝ) / 5) with hAdef
  set B := Real.log N ^ ((1:ℝ) / 5) with hB
  set C := Real.log N ^ ((6:ℝ) / 5) with hCdef
  have hApos : 0 < A := by positivity
  have hBpos : 0 < B := by positivity
  have hlq : Real.log q * Real.log N ≤ 0.0001 * A * C := by
    have e1 : Real.log q * Real.log N ≤ Real.log N * Real.log N :=
      mul_le_mul_of_nonneg_right h4 hL0.le
    have e2 : 0.0001 * (10000 * Real.log N) * Real.log N ≤ 0.0001 * A * C := by
      have := mul_le_mul hA hC hL0.le hApos.le
      nlinarith
    nlinarith
  calc A * B * Real.log q * Real.log N = (A * B) * (Real.log q * Real.log N) := by ring
    _ ≤ (A * B) * (0.0001 * A * C) := mul_le_mul_of_nonneg_left hlq (by positivity)
    _ = 0.0001 * (A * A) * (B * C) := by ring

lemma core_n66b {N q : ℝ} (hN : 0 < N) (hL : 3100 ≤ Real.log N)
    (hq1 : (0.28 / 1.0012) ^ 2 * Real.log N ^ 4 < q)
    (hq2 : q < (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5) :
    N ^ ((2:ℝ) / 5) * Real.log N ^ (-(4:ℝ) / 5) * (N ^ ((2:ℝ) / 5) * Real.log N ^ ((1:ℝ) / 5)) *
      Real.log q * Real.log (N ^ ((2:ℝ) / 5) * Real.log N ^ (-(4:ℝ) / 5) *
        (N ^ ((2:ℝ) / 5) * Real.log N ^ ((1:ℝ) / 5))) ≤
      0.8 * N ^ ((4:ℝ) / 5) * Real.log N ^ (1.4 : ℝ) := by
  obtain ⟨h1, h2, h3, h4⟩ := q_facts hN hL hq1 hq2
  have hL0 : 0 < Real.log N := by linarith
  rw [UV_eq hN hL0]
  obtain ⟨hY0, hY1⟩ := logUV hN hL
  have hL14 : Real.log N ^ (1.4 : ℝ) = Real.log N ^ (-(3:ℝ) / 5) * Real.log N ^ 2 := by
    rw [show (1.4:ℝ) = -(3:ℝ) / 5 + ((2:ℕ):ℝ) by norm_num, Real.rpow_add hL0, Real.rpow_natCast]
  rw [hL14]
  have hD : 0 < Real.log N ^ (-(3:ℝ) / 5) := by positivity
  have hm := mul_le_mul h4 hY1 hY0 hL0.le
  calc N ^ ((4:ℝ) / 5) * Real.log N ^ (-(3:ℝ) / 5) * Real.log q *
        Real.log (N ^ ((4:ℝ) / 5) * Real.log N ^ (-(3:ℝ) / 5))
      = (N ^ ((4:ℝ) / 5) * Real.log N ^ (-(3:ℝ) / 5)) *
        (Real.log q * Real.log (N ^ ((4:ℝ) / 5) * Real.log N ^ (-(3:ℝ) / 5))) := by ring
    _ ≤ (N ^ ((4:ℝ) / 5) * Real.log N ^ (-(3:ℝ) / 5)) * (Real.log N * (0.8 * Real.log N)) :=
        mul_le_mul_of_nonneg_left hm (by positivity)
    _ = 0.8 * N ^ ((4:ℝ) / 5) * (Real.log N ^ (-(3:ℝ) / 5) * Real.log N ^ 2) := by ring

lemma s_big {N q : ℝ} (hL : 3100 ≤ Real.log N)
    (hq1 : (0.28 / 1.0012) ^ 2 * Real.log N ^ 4 < q) : 2600000 ≤ √q := by
  have h := sqrtq_lb hL hq1
  have : (3100:ℝ) ^ 2 ≤ Real.log N ^ 2 := pow_le_pow_left₀ (by norm_num) hL 2
  have h2 : (2600000:ℝ) ≤ (0.28 / 1.0012) * 3100 ^ 2 := by norm_num
  have := mul_le_mul_of_nonneg_left this (by norm_num : (0:ℝ) ≤ 0.28 / 1.0012)
  linarith

lemma core_n65c {N q : ℝ} (hN : 0 < N) (hL : 3100 ≤ Real.log N)
    (hq1 : (0.28 / 1.0012) ^ 2 * Real.log N ^ 4 < q)
    (hq2 : q < (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5) :
    5 * N / q * Real.log (N ^ ((2:ℝ) / 5) * Real.log N ^ ((1:ℝ) / 5)) * Real.log N ≤
      0.0282 * N / √q * Real.log N ^ 2 := by
  obtain ⟨h1, h2, h3, h4⟩ := q_facts hN hL hq1 hq2
  have hL0 : 0 < Real.log N := by linarith
  have hq0 : 0 < q := by linarith
  have hsb := s_big hL hq1
  have hs0 : 0 < √q := by linarith
  have hX := logV hN hL
  have key : 3 * N * Real.log N ^ 2 * √q ≤ 0.0282 * N * Real.log N ^ 2 * q := by
    calc 3 * N * Real.log N ^ 2 * √q ≤ 0.0282 * N * Real.log N ^ 2 * (√q * √q) := by
          have := mul_nonneg (mul_nonneg hN.le (sq_nonneg (Real.log N))) hs0.le
          nlinarith [mul_le_mul_of_nonneg_left hsb this]
      _ = 0.0282 * N * Real.log N ^ 2 * q := by rw [Real.mul_self_sqrt hq0.le]
  calc 5 * N / q * Real.log (N ^ ((2:ℝ) / 5) * Real.log N ^ ((1:ℝ) / 5)) * Real.log N
      ≤ 5 * N / q * (0.6 * Real.log N) * Real.log N :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hX (by positivity)) hL0.le
    _ = (3 * N * Real.log N ^ 2) / q := by ring
    _ ≤ (0.0282 * N * Real.log N ^ 2) / √q := by
        rw [div_le_div_iff₀ hq0 hs0]; exact key
    _ = 0.0282 * N / √q * Real.log N ^ 2 := by ring

lemma core_n66c {N q : ℝ} (hN : 0 < N) (hL : 3100 ≤ Real.log N)
    (hq1 : (0.28 / 1.0012) ^ 2 * Real.log N ^ 4 < q)
    (hq2 : q < (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5) :
    5 * N / q * Real.log (N ^ ((2:ℝ) / 5) * Real.log N ^ (-(4:ℝ) / 5) *
        (N ^ ((2:ℝ) / 5) * Real.log N ^ ((1:ℝ) / 5))) *
      Real.log (N ^ ((2:ℝ) / 5) * Real.log N ^ (-(4:ℝ) / 5) *
        (N ^ ((2:ℝ) / 5) * Real.log N ^ ((1:ℝ) / 5))) ≤
      0.0131 * N / √q * Real.log N ^ 2 := by
  obtain ⟨h1, h2, h3, h4⟩ := q_facts hN hL hq1 hq2
  have hL0 : 0 < Real.log N := by linarith
  have hq0 : 0 < q := by linarith
  have hsb := s_big hL hq1
  have hs0 : 0 < √q := by linarith
  rw [UV_eq hN hL0]
  obtain ⟨hY0, hY1⟩ := logUV hN hL
  have hYY : Real.log (N ^ ((4:ℝ) / 5) * Real.log N ^ (-(3:ℝ) / 5)) *
      Real.log (N ^ ((4:ℝ) / 5) * Real.log N ^ (-(3:ℝ) / 5)) ≤ 0.64 * Real.log N ^ 2 := by
    nlinarith [mul_le_mul hY1 hY1 hY0 (by positivity : (0:ℝ) ≤ 0.8 * Real.log N)]
  have key : 3.2 * N * Real.log N ^ 2 * √q ≤ 0.0131 * N * Real.log N ^ 2 * q := by
    calc 3.2 * N * Real.log N ^ 2 * √q ≤ 0.0131 * N * Real.log N ^ 2 * (√q * √q) := by
          have := mul_nonneg (mul_nonneg hN.le (sq_nonneg (Real.log N))) hs0.le
          nlinarith [mul_le_mul_of_nonneg_left hsb this]
      _ = 0.0131 * N * Real.log N ^ 2 * q := by rw [Real.mul_self_sqrt hq0.le]
  calc 5 * N / q * Real.log (N ^ ((4:ℝ) / 5) * Real.log N ^ (-(3:ℝ) / 5)) *
        Real.log (N ^ ((4:ℝ) / 5) * Real.log N ^ (-(3:ℝ) / 5))
      = 5 * N / q * (Real.log (N ^ ((4:ℝ) / 5) * Real.log N ^ (-(3:ℝ) / 5)) *
        Real.log (N ^ ((4:ℝ) / 5) * Real.log N ^ (-(3:ℝ) / 5))) := by ring
    _ ≤ 5 * N / q * (0.64 * Real.log N ^ 2) := mul_le_mul_of_nonneg_left hYY (by positivity)
    _ = (3.2 * N * Real.log N ^ 2) / q := by ring
    _ ≤ (0.0131 * N * Real.log N ^ 2) / √q := by
        rw [div_le_div_iff₀ hq0 hs0]; exact key
    _ = 0.0131 * N / √q * Real.log N ^ 2 := by ring

lemma core_S1 {N : ℝ} (hN : 0 < N) (hL : 3100 ≤ Real.log N) :
    1.02 * (N ^ ((2:ℝ) / 5) * Real.log N ^ (-(4:ℝ) / 5)) ≤
      0.38 * N ^ ((4:ℝ) / 5) * Real.log N ^ (1.4 : ℝ) := by
  have hL0 : 0 < Real.log N := by linarith
  have hN1 : 1 ≤ N := by
    by_contra h
    push_neg at h
    have := Real.log_neg hN h
    linarith
  have h1 : Real.log N ^ (-(4:ℝ) / 5) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  have h2 : N ^ ((2:ℝ) / 5) ≤ N ^ ((4:ℝ) / 5) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  have h3 : Real.log N ≤ Real.log N ^ (1.4 : ℝ) := by
    calc Real.log N = Real.log N ^ (1:ℝ) := (Real.rpow_one _).symm
      _ ≤ Real.log N ^ (1.4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hA : 0 < N ^ ((2:ℝ) / 5) := by positivity
  have h4 : N ^ ((2:ℝ) / 5) * Real.log N ^ (-(4:ℝ) / 5) ≤ N ^ ((2:ℝ) / 5) := by
    nlinarith
  have h5 : N ^ ((2:ℝ) / 5) * 3100 ≤ N ^ ((4:ℝ) / 5) * Real.log N ^ (1.4 : ℝ) := by
    have := mul_le_mul h2 (le_trans hL h3) (by norm_num) (by positivity)
    exact this
  nlinarith

lemma pos_of_log {N : ℕ} (hL : 3100 ≤ Real.log N) : (0:ℝ) < N := by
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h
    norm_num at hL
  · exact_mod_cast h


end VaBAux

open LL_Decomp1543c in
theorem solution (N : ℕ) (hL : 3100 ≤ Real.log N) (q : ℕ)
    (hq1 : (0.28 / 1.0012) ^ 2 * Real.log N ^ 4 < q)
    (hq2 : (q : ℝ) < (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5) :
    Vf N * Real.log q * Real.log N ≤ 0.0001 * (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log N ^ (1.4 : ℝ):= by
  have hN := VaBAux.pos_of_log hL
  exact VaBAux.core_n65b hN hL hq1 hq2
