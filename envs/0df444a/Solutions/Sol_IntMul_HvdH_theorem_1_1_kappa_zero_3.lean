-- Prove2me | solution 3 for IntMul.HvdH.theorem_1_1_kappa_zero
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-09T08:49:40.88899+00:00
-- url     : https://prove2.me/submissions/7f6f05be-0649-4cbc-8447-3e0a000f7673
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Data.Nat.Log
import Mathlib.Tactic
import Theorems.Thm_IntMul_HvdH_proposition_5_4
import Theorems.Thm_IntMul_multipliesAt_sInf
import Theorems.Thm_Complexity_contracting_recurrence_bounded

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
theorem normalized_recurrence (d : ℕ) (hd : 2 ≤ d) :
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


namespace IntMulBudget
lemma multipliesAt_mono {M : MultitapeTM} {n : ℕ} {τ τ' : ℝ}
    (h : MultipliesAt M n τ) (hle : τ ≤ τ') : MultipliesAt M n τ' := by
  intro x y hx hy
  obtain ⟨t, ht, hh⟩ := h x y hx hy
  exact ⟨t, ht.trans hle, hh⟩
end IntMulBudget
namespace IntMulThm11
/-- `1296 b² < 2^(b-1)` once `b ≥ 30`. -/
lemma sq_lt_two_pow (b : ℕ) (hb : 30 ≤ b) : 1296 * b ^ 2 < 2 ^ (b - 1) := by
  induction b, hb using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [show k + 1 - 1 = (k - 1) + 1 by omega,
      show (2 : ℕ) ^ (k - 1 + 1) = 2 ^ (k - 1) * 2 from pow_succ 2 (k - 1)]
    nlinarith

/-- The parameters `T` and `r` of §5.1 exist. -/
lemma exists_T_r (n b d : ℕ) (hb : 1 ≤ b) (hbn : b ≤ n) (hd : 1 ≤ d) :
    ∃ T r : ℕ, (∃ k : ℕ, T = 2 ^ k) ∧ 4 * (n : ℝ) / b ≤ T ∧ (T : ℝ) < 8 * (n : ℝ) / b ∧
      (∃ j : ℕ, r = 2 ^ j) ∧ (T : ℝ) ^ ((1 : ℝ) / d) ≤ r ∧ (r : ℝ) < 2 * (T : ℝ) ^ ((1 : ℝ) / d) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hn1 : (1 : ℝ) ≤ n / b := by
    rw [le_div_iff₀ hbR]; simpa using (show ((b : ℕ) : ℝ) ≤ n by exact_mod_cast hbn)
  have hexT : ∃ k : ℕ, 4 * (n : ℝ) / b ≤ (2 : ℝ) ^ k := by
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (4 * (n : ℝ) / b) (by norm_num : (1 : ℝ) < 2)
    exact ⟨k, hk.le⟩
  classical
  set k := Nat.find hexT
  have hk := Nat.find_spec hexT
  have hTlt : (2 : ℝ) ^ k < 8 * (n : ℝ) / b := by
    rcases Nat.eq_zero_or_eq_succ_pred k with h0 | hs
    · rw [h0]; have : (8 : ℝ) * n / b = 8 * (n / b) := by ring
      rw [this]; norm_num; linarith
    · have hmin := Nat.find_min hexT (show k.pred < k by omega)
      rw [not_le] at hmin
      rw [hs, pow_succ]
      have : (8 : ℝ) * n / b = 2 * (4 * n / b) := by ring
      rw [this]; linarith
  set T : ℕ := 2 ^ k
  have hT1 : (1 : ℝ) ≤ T := by simp only [T]; push_cast; exact one_le_pow₀ (by norm_num)
  have hdR : (0 : ℝ) < 1 / d := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    positivity
  have hTd1 : (1 : ℝ) ≤ (T : ℝ) ^ ((1 : ℝ) / d) := Real.one_le_rpow hT1 hdR.le
  have hexr : ∃ j : ℕ, (T : ℝ) ^ ((1 : ℝ) / d) ≤ (2 : ℝ) ^ j := by
    obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt ((T : ℝ) ^ ((1 : ℝ) / d)) (by norm_num : (1 : ℝ) < 2)
    exact ⟨j, hj.le⟩
  set j := Nat.find hexr
  have hj := Nat.find_spec hexr
  have hrlt : (2 : ℝ) ^ j < 2 * (T : ℝ) ^ ((1 : ℝ) / d) := by
    rcases Nat.eq_zero_or_eq_succ_pred j with h0 | hs
    · rw [h0, pow_zero]; linarith
    · have hmin := Nat.find_min hexr (show j.pred < j by omega)
      rw [not_le] at hmin
      rw [hs, pow_succ]; linarith
  refine ⟨T, 2 ^ j, ⟨k, rfl⟩, ?_, ?_, ⟨j, rfl⟩, ?_, ?_⟩
  · simpa [T] using hk
  · simpa [T] using hTlt
  · push_cast; exact hj
  · push_cast; exact hrlt


end IntMulThm11

open IntMulThm11 in
theorem logarithmic_time_bound : MulTimeBound fun n => (n : ℝ) * Real.log n := by
  obtain ⟨M, hcorr, A, hrec⟩ := normalized_recurrence 1729 (by norm_num)
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = 1729 ^ 12 := ⟨_, rfl⟩
  have hK30 : 30 ≤ K := by rw [hK]; norm_num
  rw [← hK] at hrec
  set N0 : ℕ := 2 ^ K with hN0
  set W : ℕ → ℝ := fun m => sInf {τ : ℝ | MultipliesAt M m τ} with hW
  set Tn : ℕ → ℝ := fun m => W m / ((m : ℝ) * Real.log m) with hTn
  have hN0big : 2 < N0 := by
    rw [hN0]
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcontract : ∀ n : ℕ, N0 ≤ n → 2 ≤ n →
      ∃ m : ℕ, 2 ≤ m ∧ m < n ∧
        Tn n ≤ (1728 : ℝ) / ((1729 : ℝ) - 1 / 2) * Tn m + A := by
    intro n hnN hn2
    set b := Nat.clog 2 n with hb_def
    have hb_big : K ≤ b := by
      have := Nat.clog_mono_right 2 hnN
      rw [hN0, Nat.clog_pow 2 K (by norm_num)] at this
      exact this
    have hb30 : 30 ≤ b := le_trans hK30 hb_big
    have hbn : b ≤ n := by
      rw [hb_def]; exact Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
    obtain ⟨T, r, hTpow, hT1, hT2, hrpow, hr1, hr2⟩ :=
      exists_T_r n b 1729 (by omega) hbn (by norm_num)
    set p := 6 * b with hp_def
    set m := 3 * r * p with hm_def
    have hr1' : 1 ≤ r := by obtain ⟨j, rfl⟩ := hrpow; exact Nat.one_le_two_pow
    have hm2 : 2 ≤ m := by
      rw [hm_def, hp_def]; nlinarith
    -- 3rp < n
    have hmn : m < n := by
      have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      have hbR : (8 : ℝ) ≤ b := by exact_mod_cast (show 8 ≤ b by omega)
      have hbpos : (0 : ℝ) < b := by linarith
      have hTn : (T : ℝ) ≤ n := by
        have : 8 * (n : ℝ) / b ≤ n := by
          rw [div_le_iff₀ hbpos]; nlinarith
        linarith
      have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg _
      have hroot : (T : ℝ) ^ ((1 : ℝ) / 1729) ≤ Real.sqrt n := by
        rw [Real.sqrt_eq_rpow]
        calc (T : ℝ) ^ ((1 : ℝ) / 1729) ≤ (n : ℝ) ^ ((1 : ℝ) / 1729) :=
              Real.rpow_le_rpow hT0 hTn (by norm_num)
          _ ≤ (n : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le hnR (by norm_num)
      have hsq : ((36 * b : ℕ) : ℝ) ≤ Real.sqrt n := by
        apply Real.le_sqrt_of_sq_le
        have h1 := sq_lt_two_pow b hb30
        have h2 := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (show 1 < n by omega)
        rw [← hb_def] at h2
        have : (36 * b) ^ 2 < n := by
          calc (36 * b) ^ 2 = 1296 * b ^ 2 := by ring
            _ < 2 ^ (b - 1) := h1
            _ = 2 ^ b.pred := rfl
            _ < n := h2
        exact_mod_cast this.le
      have hmR : (m : ℝ) < n := by
        have hsqrt0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
        have hmexp : (m : ℝ) = 18 * b * r := by rw [hm_def, hp_def]; push_cast; ring
        calc (m : ℝ) = 18 * b * r := hmexp
          _ < 18 * b * (2 * (T : ℝ) ^ ((1 : ℝ) / 1729)) := by
              have : (0 : ℝ) < 18 * b := by positivity
              exact mul_lt_mul_of_pos_left (by simpa using hr2) this
          _ = (36 * b : ℝ) * (T : ℝ) ^ ((1 : ℝ) / 1729) := by ring
          _ ≤ (36 * b : ℝ) * Real.sqrt n := by gcongr
          _ ≤ Real.sqrt n * Real.sqrt n := by
              gcongr; push_cast at hsq; exact hsq
          _ = n := Real.mul_self_sqrt (Nat.cast_nonneg _)
      exact_mod_cast hmR
    have hstep := hrec n hnN b p T r hb_def rfl hTpow hT1 hT2 hrpow
      (by simpa using hr1) (by simpa using hr2)
    refine ⟨m, hm2, hmn, ?_⟩
    exact (show Tn n < (1728 : ℝ) / ((1729 : ℝ) - 1 / 2) * Tn m + A by
      simpa [hTn, hW, hm_def] using hstep).le
  obtain ⟨C, hC, hmain⟩ := Complexity.contracting_recurrence_bounded Tn 2 N0
    ((1728 : ℝ) / ((1729 : ℝ) - 1 / 2)) A (by norm_num) (by norm_num) hcontract
  -- conclude
  refine ⟨M, hcorr, C, hC, 2, fun n hn _ => ?_⟩
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hden : 0 < (n : ℝ) * Real.log n := mul_pos hnpos hlog
  have hTle := hmain n hn
  have hWle : W n ≤ C * ((n : ℝ) * Real.log n) := by
    have := (div_le_iff₀ hden).1 (by simpa [hTn] using hTle)
    simpa [hW] using this
  exact IntMulBudget.multipliesAt_mono (IntMul.multipliesAt_sInf (hcorr n (by omega))) hWle


theorem solution : KappaBound 0 := by
  obtain ⟨M, hcorr, c, hc, n₀, hM⟩ := logarithmic_time_bound
  refine ⟨M, hcorr, c, hc, n₀, fun n hn h1n => ?_⟩
  -- ln n ≤ ⌈log₂ n⌉ · ln 2 ≤ lg n
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast h1n
  have hlog : Real.log n ≤ (lg n : ℝ) := by
    have h1 : ((n : ℕ) : ℝ) ≤ ((2 ^ Nat.clog 2 n : ℕ) : ℝ) :=
      by exact_mod_cast Nat.le_pow_clog (by norm_num) n
    have h2 := Real.log_le_log (by linarith) h1
    push_cast at h2
    rw [Real.log_pow] at h2
    have hl2 := Real.log_two_lt_d9
    have h3 : ((Nat.clog 2 n : ℕ) : ℝ) ≤ (lg n : ℝ) := by
      exact_mod_cast le_max_left _ _
    have h4 : ((Nat.clog 2 n : ℕ) : ℝ) * Real.log 2 ≤ (Nat.clog 2 n : ℝ) :=
      mul_le_of_le_one_right (Nat.cast_nonneg _) (by linarith)
    linarith
  intro x y hx hy
  obtain ⟨t, ht, hh⟩ := hM n hn h1n x y hx hy
  refine ⟨t, ht.trans ?_, hh⟩
  simp only [sub_zero, Real.rpow_one]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog (by linarith)) hc.le
