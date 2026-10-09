-- Prove2me | solution 1 for IntMul.HvdH.rosser_schoenfeld_theta_upper
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @avi
-- created : 2026-10-09T02:24:56.706913+00:00
-- url     : https://prove2.me/submissions/8c26e84f-d69f-414f-a928-de3a01488606
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_TaoFivePrimes_dusart_theta_error_log_four_chebyshev

open Real

namespace RSUpper

/-- Sieving primes: every composite `n ≤ 1000` has a prime factor in this list. -/
def P0 : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]

/-- Candidates: `n ≥ 2` with no proper divisor in `P0`. Every prime is a candidate. -/
def cand (n : ℕ) : Bool := decide (2 ≤ n) && P0.all fun q => n % q != 0 || q == n

lemma cand_of_prime {n : ℕ} (hn : n.Prime) : cand n = true := by
  unfold cand
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
    bne_iff_ne, ne_eq, beq_iff_eq]
  refine ⟨hn.two_le, fun q hq => ?_⟩
  by_cases h : n % q = 0
  · right
    rcases hn.eq_one_or_self_of_dvd q (Nat.dvd_of_mod_eq_zero h) with h1 | h1
    · simp [P0] at hq; omega
    · exact h1
  · left; exact h

lemma two_le_of_cand {n : ℕ} (h : cand n = true) : 2 ≤ n := by
  unfold cand at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

/-- Product of the candidates up to `b`; it is a multiple of the primorial of `b`. -/
def candProd (b : ℕ) : ℕ := ((List.range (b + 1)).filter cand).prod

lemma candProd_pos (b : ℕ) : 0 < candProd b := by
  unfold candProd
  apply List.prod_pos
  intro n hn
  have := two_le_of_cand (List.mem_filter.1 hn).2
  omega

lemma theta_le_log_candProd (b : ℕ) : Chebyshev.theta b ≤ Real.log (candProd b) := by
  have hnd : ((List.range (b + 1)).filter cand).Nodup := (List.nodup_range).filter _
  rw [Chebyshev.theta_eq_sum_primesLE_log]
  have hprod : candProd b = ∏ n ∈ ((List.range (b + 1)).filter cand).toFinset, n := by
    unfold candProd; rw [List.prod_toFinset _ hnd, List.map_id']
  rw [hprod, Nat.cast_prod, Real.log_prod]
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      rw [Nat.mem_primesLE] at hp
      rw [List.mem_toFinset, List.mem_filter, List.mem_range]
      exact ⟨by omega, cand_of_prime hp.2⟩
    · intro n _ _
      exact Real.log_natCast_nonneg n
  · intro n hn
    rw [List.mem_toFinset, List.mem_filter] at hn
    have := two_le_of_cand hn.2
    exact_mod_cast (show n ≠ 0 by omega)

/-- One certified segment `[a, b]` of the finite range. -/
lemma seg (a b jt mt jb mb : ℕ) (hjt : 0 < jt) (hjb : 0 < jb)
    (hT : candProd b ^ jt ≤ 2 ^ mt) (hB : b ^ jb ≤ 2 ^ mb) (ha : 563 ≤ a)
    (hnum : (mt : ℝ) / jt * 0.6931471808 <
      a * (1 + 1 / (2 * ((mb : ℝ) / jb * 0.6931471808))))
    (y : ℝ) (hay : (a : ℝ) ≤ y) (hyb : y ≤ b) :
    Chebyshev.theta y < y + y / (2 * Real.log y) := by
  have h2hi := Real.log_two_lt_d9
  have h2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hjt' : (0 : ℝ) < jt := by exact_mod_cast hjt
  have hjb' : (0 : ℝ) < jb := by exact_mod_cast hjb
  have ha' : (563 : ℝ) ≤ a := by exact_mod_cast ha
  -- upper bound for θ(y)
  have hθ : Chebyshev.theta y ≤ (mt : ℝ) / jt * 0.6931471808 := by
    have h1 : Chebyshev.theta y ≤ Chebyshev.theta b := Chebyshev.theta_mono hyb
    have h2 := theta_le_log_candProd b
    have hN : (0 : ℝ) < candProd b := by exact_mod_cast candProd_pos b
    have h3 : Real.log (((candProd b : ℕ) : ℝ) ^ jt) ≤ Real.log ((2 : ℝ) ^ mt) :=
      Real.log_le_log (by positivity) (by exact_mod_cast hT)
    rw [Real.log_pow, Real.log_pow] at h3
    have h4 : Real.log (candProd b) ≤ (mt : ℝ) / jt * Real.log 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hjt']; linarith
    have h5 : (mt : ℝ) / jt * Real.log 2 ≤ (mt : ℝ) / jt * 0.6931471808 :=
      mul_le_mul_of_nonneg_left h2hi.le (by positivity)
    linarith
  -- upper bound for log b
  have hb' : (563 : ℝ) ≤ b := ha'.trans (hay.trans hyb)
  set U := (mb : ℝ) / jb * 0.6931471808 with hUdef
  have hU : Real.log b ≤ U := by
    have h1 : Real.log ((b : ℝ) ^ jb) ≤ Real.log ((2 : ℝ) ^ mb) :=
      Real.log_le_log (by positivity) (by exact_mod_cast hB)
    rw [Real.log_pow, Real.log_pow] at h1
    have h2 : Real.log b ≤ (mb : ℝ) / jb * Real.log 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hjb']; linarith
    have h3 : (mb : ℝ) / jb * Real.log 2 ≤ U :=
      mul_le_mul_of_nonneg_left h2hi.le (by positivity)
    linarith
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hlogyb : Real.log y ≤ Real.log b := Real.log_le_log (by linarith) hyb
  have hUpos : 0 < U := by linarith
  have hk : y / (2 * U) ≤ y / (2 * Real.log y) :=
    div_le_div_of_nonneg_left (by linarith) (by positivity) (by linarith)
  have hc : 0 ≤ 1 + 1 / (2 * U) := by positivity
  have hmono : (a : ℝ) * (1 + 1 / (2 * U)) ≤ y * (1 + 1 / (2 * U)) :=
    mul_le_mul_of_nonneg_right hay hc
  have : y * (1 + 1 / (2 * U)) = y + y / (2 * U) := by field_simp
  linarith

theorem finite_range (y : ℝ) (h1 : 563 ≤ y) (h2 : y ≤ 1000) :
    Chebyshev.theta y < y + y / (2 * Real.log y) := by
  rcases le_or_gt y 640 with h0 | h0
  · exact seg 563 640 24 20827 31 289 (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) y (by norm_num; linarith) (by norm_num; linarith)
  rcases le_or_gt y 726 with h1 | h1
  · exact seg 640 726 40 39597 39 371 (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) y (by norm_num; linarith) (by norm_num; linarith)
  rcases le_or_gt y 822 with h2 | h2
  · exact seg 726 822 34 38221 19 184 (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) y (by norm_num; linarith) (by norm_num; linarith)
  rcases le_or_gt y 928 with h3 | h3
  · exact seg 822 928 20 25411 36 355 (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) y (by norm_num; linarith) (by norm_num; linarith)
  exact seg 928 1000 7 9657 30 299 (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) y (by norm_num; linarith) (by norm_num; linarith)

/-- `log 1000 > 6.72`, via `log 1000 = 9 log 2 + log (1000/512)` and `log x ≥ 1 - 1/x`. -/
lemma log_1000_gt : (6.72 : ℝ) < Real.log 1000 := by
  have h2 := Real.log_two_gt_d9
  have h1 : 1 - (1000 / 512 : ℝ)⁻¹ ≤ Real.log (1000 / 512) :=
    Real.one_sub_inv_le_log_of_pos (by norm_num)
  have h3 : Real.log 1000 = 9 * Real.log 2 + Real.log (1000 / 512) := by
    have e : (1000 : ℝ) = 2 ^ 9 * (1000 / 512) := by norm_num
    conv_lhs => rw [e]
    rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow]; norm_num
  rw [h3]; norm_num at h1 ⊢; linarith

theorem tail (y : ℝ) (hy : 1000 ≤ y) :
    Chebyshev.theta y < y + y / (2 * Real.log y) := by
  have hD := TaoFivePrimes.dusart_theta_error_log_four_chebyshev y (by linarith)
  have hL : (6.72 : ℝ) < Real.log y :=
    log_1000_gt.trans_le (Real.log_le_log (by norm_num) hy)
  have hLpos : 0 < Real.log y := by linarith
  have hypos : 0 < y := by linarith
  have hcube : (302.6 : ℝ) < Real.log y ^ 3 := by
    have : (6.72 : ℝ) ^ 3 < Real.log y ^ 3 := pow_lt_pow_left₀ hL (by norm_num) (by norm_num)
    norm_num at this ⊢; linarith
  -- 151.3 y / L⁴ < y / (2 L)
  have hkey : (1513 / 10 : ℝ) * y / Real.log y ^ 4 < y / (2 * Real.log y) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    have : (1513 / 10 : ℝ) * y * (2 * Real.log y) = y * Real.log y * 302.6 := by ring
    have h4 : y * Real.log y ^ 4 = y * Real.log y * Real.log y ^ 3 := by ring
    rw [this, h4]
    exact mul_lt_mul_of_pos_left hcube (by positivity)
  have := (abs_le.1 hD).2
  linarith

end RSUpper

theorem solution (y : ℝ) (hy : 563 ≤ y) :
    Chebyshev.theta y < y + y / (2 * Real.log y) := by
  rcases le_or_gt y 1000 with h | h
  · exact RSUpper.finite_range y hy h
  · exact RSUpper.tail y h.le
