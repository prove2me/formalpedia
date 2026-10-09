-- Prove2me | solution 1 for IntMul.HvdH.corollary_5_5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @avi
-- created : 2026-10-09T00:41:43.244985+00:00
-- url     : https://prove2.me/submissions/2b390472-21ed-48ba-9fc7-ba21930163b1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_IntMul_HvdH_proposition_5_4

open Real IntMul IntMul.HvdH

namespace IntMulCor55

/-- `2 d² log(36 b) ≤ (b - 1) log 2` whenever `d ≥ 2` and `d¹² ≤ b`. -/
lemma key_log (d b : ℕ) (hd : 2 ≤ d) (hb : d ^ 12 ≤ b) :
    2 * (d : ℝ) ^ 2 * Real.log (36 * b) ≤ ((b : ℝ) - 1) * Real.log 2 := by
  have hb0 : (0 : ℝ) ≤ b := by positivity
  set s : ℝ := (b : ℝ) ^ (((12 : ℕ) : ℝ)⁻¹) with hs
  have hs0 : 0 ≤ s := Real.rpow_nonneg hb0 _
  have hs12 : s ^ 12 = b := Real.rpow_inv_natCast_pow hb0 (by norm_num)
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hds : (d : ℝ) ≤ s := by
    by_contra h
    rw [not_le] at h
    have h1 : s ^ 12 < (d : ℝ) ^ 12 := pow_lt_pow_left₀ h hs0 (by norm_num)
    have h2 : ((d ^ 12 : ℕ) : ℝ) ≤ b := by exact_mod_cast hb
    push_cast at h2
    linarith
  have hs2 : 2 ≤ s := hd'.trans hds
  have hspos : 0 < s := by linarith
  have hlogb : Real.log b = 12 * Real.log s := by
    rw [← hs12, Real.log_pow]; norm_num
  have hlogs : Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos hspos
  have hlog36 : Real.log 36 < 4 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have he := Real.exp_one_gt_d9
    have : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    have := pow_lt_pow_left₀ he (by norm_num) (by norm_num : (4 : ℕ) ≠ 0)
    norm_num at this ⊢; linarith
  have hbpos : (0 : ℝ) < b := by rw [← hs12]; positivity
  have hlog : Real.log (36 * b) ≤ 12 * s := by
    rw [Real.log_mul (by norm_num) hbpos.ne', hlogb]; linarith
  have hl2 := Real.log_two_gt_d9
  have hs9 : (512 : ℝ) ≤ s ^ 9 := by
    have := pow_le_pow_left₀ (by norm_num) hs2 9; norm_num at this; linarith
  have hd2 : (d : ℝ) ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ (by linarith) hds 2
  have hs3 : 0 ≤ s ^ 3 := by positivity
  have e1 : 2 * (d : ℝ) ^ 2 * Real.log (36 * b) ≤ 24 * s ^ 3 := by
    have : 0 ≤ Real.log (36 * b) := Real.log_nonneg (by nlinarith)
    nlinarith
  have e2 : 24 * s ^ 3 ≤ (s ^ 12 - 1) * 0.6931471803 := by
    have : s ^ 12 = s ^ 9 * s ^ 3 := by ring
    rw [this]; nlinarith
  have e3 : (s ^ 12 - 1) * 0.6931471803 ≤ (s ^ 12 - 1) * Real.log 2 := by
    apply mul_le_mul_of_nonneg_left hl2.le
    have : (512 : ℝ) * 8 ≤ s ^ 12 := by
      have : s ^ 12 = s ^ 9 * s ^ 3 := by ring
      have h8 : (8 : ℝ) ≤ s ^ 3 := by
        have := pow_le_pow_left₀ (by norm_num) hs2 3; norm_num at this; linarith
      rw [this]; nlinarith
    linarith
  have hbs : (b : ℝ) - 1 = s ^ 12 - 1 := by rw [hs12]
  rw [hbs]; linarith

end IntMulCor55

open IntMulCor55 in
theorem solution (d : ℕ) (hd : 2 ≤ d) :
    ∃ M : MultitapeTM, (∀ n : ℕ, 1 ≤ n → ∃ τ : ℝ, MultipliesAt M n τ) ∧
      ∃ A : ℝ, ∀ n : ℕ, 2 ^ (d ^ 12) ≤ n →
        ∀ b p T r : ℕ, b = Nat.clog 2 n → p = 6 * b →
          (∃ k : ℕ, T = 2 ^ k) → 4 * (n : ℝ) / b ≤ T → (T : ℝ) < 8 * (n : ℝ) / b →
          (∃ j : ℕ, r = 2 ^ j) → (T : ℝ) ^ ((1 : ℝ) / d) ≤ r → (r : ℝ) < 2 * (T : ℝ) ^ ((1 : ℝ) / d) →
          sInf {τ : ℝ | MultipliesAt M n τ} / ((n : ℝ) * Real.log n) <
            1728 / ((d : ℝ) - 1 / 2) *
              (sInf {τ : ℝ | MultipliesAt M (3 * r * p) τ} /
                (((3 * r * p : ℕ) : ℝ) * Real.log ((3 * r * p : ℕ) : ℝ))) + A := by
  obtain ⟨M, hcorr, C, hrec⟩ := IntMul.HvdH.proposition_5_4 d hd
  refine ⟨M, hcorr, C, ?_⟩
  intro n hn b p T r hb hp hTpow hT1 hT2 hrpow hr1 hr2
  have hP := hrec n hn b p T r hb hp hTpow hT1 hT2 hrpow hr1 hr2
  -- sizes
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd12 : 4096 ≤ d ^ 12 := by
    have := Nat.pow_le_pow_left hd 12; norm_num at this; omega
  have hbd : d ^ 12 ≤ b := by
    rw [hb, ← Nat.clog_pow 2 (d ^ 12) (by norm_num)]
    exact Nat.clog_mono_right 2 hn
  have hb4096 : 4096 ≤ b := hd12.trans hbd
  have hbR : (4096 : ℝ) ≤ b := by exact_mod_cast hb4096
  have hn2 : 2 ≤ n := le_trans (Nat.succ_le_of_lt (Nat.one_lt_two_pow (by positivity) : 1 < 2 ^ (d ^ 12))) hn
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hnpos : (0 : ℝ) < n := by linarith
  -- log n ≥ (b - 1) log 2
  have hpow : 2 ^ (Nat.clog 2 n).pred < n := Nat.pow_pred_clog_lt_self (by norm_num) hn2
  rw [← hb] at hpow
  have hlogn : ((b : ℝ) - 1) * Real.log 2 < Real.log n := by
    have h1 : ((2 : ℕ) ^ b.pred : ℝ) < n := by exact_mod_cast hpow
    have h2 := Real.log_lt_log (by positivity) h1
    push_cast at h2
    rw [Real.log_pow] at h2
    have : ((b.pred : ℕ) : ℝ) = (b : ℝ) - 1 := by
      rw [Nat.pred_eq_sub_one, Nat.cast_sub (by omega)]; simp
    rw [this] at h2; exact h2
  have hl2 := Real.log_two_gt_d9
  have hlognpos : 0 < Real.log n := by nlinarith
  -- T facts
  obtain ⟨k, hk⟩ := hTpow
  have hT1' : (1 : ℝ) ≤ T := by rw [hk]; exact_mod_cast Nat.one_le_two_pow
  have hbpos : (0 : ℝ) < b := by linarith
  have hTb : (T : ℝ) * b < 8 * n := by rwa [lt_div_iff₀ hbpos] at hT2
  have hTn : (T : ℝ) < n := by nlinarith
  -- r facts
  obtain ⟨j, hj⟩ := hrpow
  have hr1' : (1 : ℝ) ≤ r := by rw [hj]; exact_mod_cast Nat.one_le_two_pow
  have hdpos : (0 : ℝ) < d := by linarith
  have hlogr : Real.log r < Real.log 2 + Real.log n / d := by
    have hTd : 0 < (T : ℝ) ^ ((1 : ℝ) / d) := Real.rpow_pos_of_pos (by linarith) _
    have h1 : Real.log r < Real.log (2 * (T : ℝ) ^ ((1 : ℝ) / d)) :=
      Real.log_lt_log (by linarith) hr2
    rw [Real.log_mul (by norm_num) hTd.ne', Real.log_rpow (by linarith)] at h1
    have h2 : Real.log T < Real.log n := Real.log_lt_log (by linarith) hTn
    have h3 : 1 / (d : ℝ) * Real.log T ≤ Real.log n / d := by
      rw [one_div_mul_eq_div]; exact div_le_div_of_nonneg_right h2.le hdpos.le
    linarith
  -- the size m = 3 r p = 18 r b
  subst hp
  have hm : (((3 * r * (6 * b) : ℕ)) : ℝ) = 18 * b * r := by push_cast; ring
  rw [hm]
  have hmpos : (1 : ℝ) < 18 * b * r := by nlinarith
  have hlogm : Real.log (18 * b * r) = Real.log (18 * b) + Real.log r :=
    Real.log_mul (by positivity) (by linarith)
  have h36 : Real.log (36 * b) = Real.log 2 + Real.log (18 * b) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]; ring_nf
  have hkey := key_log d b hd hbd
  -- log(36 b) ≤ log n / (2 d²)
  have hd2pos : (0 : ℝ) < 2 * (d : ℝ) ^ 2 := by positivity
  have hk2 : 2 * (d : ℝ) ^ 2 * Real.log (36 * b) ≤ Real.log n := by nlinarith
  -- (d - 1/2) log m < log n
  have hlogm_lt : ((d : ℝ) - 1 / 2) * Real.log (18 * b * r) < Real.log n := by
    have hA : Real.log (18 * b * r) < Real.log n / d + Real.log (36 * b) := by linarith
    have hpos36 : 0 ≤ Real.log (36 * b) := Real.log_nonneg (by nlinarith)
    have hdh : (0 : ℝ) < (d : ℝ) - 1 / 2 := by linarith
    calc ((d : ℝ) - 1 / 2) * Real.log (18 * b * r)
        < ((d : ℝ) - 1 / 2) * (Real.log n / d + Real.log (36 * b)) :=
          mul_lt_mul_of_pos_left hA hdh
      _ = Real.log n - Real.log n / (2 * d) + ((d : ℝ) - 1 / 2) * Real.log (36 * b) := by
          field_simp
      _ ≤ Real.log n := by
          have : ((d : ℝ) - 1 / 2) * Real.log (36 * b) ≤ Real.log n / (2 * d) := by
            rw [le_div_iff₀ (by positivity)]; nlinarith
          linarith
  have hlogmpos : 0 < Real.log (18 * b * r) := Real.log_pos hmpos
  -- nonnegativity of the time at size m
  set Mm := sInf {τ : ℝ | MultipliesAt M (3 * r * (6 * b)) τ} with hMm
  have hMm0 : 0 ≤ Mm := by
    apply Real.sInf_nonneg
    intro x hx
    obtain ⟨t, ht, -⟩ := hx (List.replicate (3 * r * (6 * b)) false) (List.replicate (3 * r * (6 * b)) false)
      (List.length_replicate) (List.length_replicate)
    exact le_trans (Nat.cast_nonneg t) ht
  set Mn := sInf {τ : ℝ | MultipliesAt M n τ}
  have hN : 0 < (n : ℝ) * Real.log n := mul_pos hnpos hlognpos
  have hdh : (0 : ℝ) < (d : ℝ) - 1 / 2 := by linarith
  have hcoef : 12 * (T : ℝ) / r / ((n : ℝ) * Real.log n) ≤
      1728 / ((d : ℝ) - 1 / 2) / (18 * b * r * Real.log (18 * b * r)) := by
    rw [div_div, div_div, div_le_div_iff₀ (by positivity) (mul_pos hdh (by positivity))]
    have hX : 0 ≤ ((d : ℝ) - 1 / 2) * Real.log (18 * b * r) := mul_nonneg hdh.le hlogmpos.le
    have h1 : 216 * ((T : ℝ) * b) * (((d : ℝ) - 1 / 2) * Real.log (18 * b * r)) ≤
        216 * (8 * n) * Real.log n :=
      mul_le_mul (by linarith) hlogm_lt.le hX (by positivity)
    have hr0 : (0 : ℝ) ≤ r := by linarith
    calc 12 * (T : ℝ) * (((d : ℝ) - 1 / 2) * (18 * b * r * Real.log (18 * b * r)))
        = r * (216 * ((T : ℝ) * b) * (((d : ℝ) - 1 / 2) * Real.log (18 * b * r))) := by ring
      _ ≤ r * (216 * (8 * n) * Real.log n) := mul_le_mul_of_nonneg_left h1 hr0
      _ = 1728 * (r * ((n : ℝ) * Real.log n)) := by ring
  calc Mn / ((n : ℝ) * Real.log n)
      < (12 * (T : ℝ) / r * Mm + C * ((n : ℝ) * Real.log n)) / ((n : ℝ) * Real.log n) :=
        div_lt_div_of_pos_right hP hN
    _ = Mm * (12 * (T : ℝ) / r / ((n : ℝ) * Real.log n)) + C := by
        field_simp
    _ ≤ Mm * (1728 / ((d : ℝ) - 1 / 2) / (18 * b * r * Real.log (18 * b * r))) + C := by
        gcongr
    _ = 1728 / ((d : ℝ) - 1 / 2) * (Mm / (18 * b * r * Real.log (18 * b * r))) + C := by
        ring
