-- Prove2me | solution 1 for LogLogJam.theorem_6_5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-26T09:15:19.990955+00:00
-- url     : https://prove2.me/submissions/33139af5-f7bf-4238-833f-e8391b863060
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_LogLogJam_eq_14
import Theorems.Thm_LogLogJam_eq_18
import Theorems.Thm_LogLogJam_lemma_6_4

open LogLogJam
open scoped ENNReal

private theorem small_iter (E : ℝ) (hE : Real.exp (Real.exp 64) ≤ E)
    (S : ℕ) (hS : (S : ℝ) < Real.log (Real.log E) / 4) :
    fIter S (1 / (8 * Real.pi * E)^2) ≤ (1/1024 : ℝ)^2 := by
  let X := (8 * Real.pi * E)^2
  have he : 0 < E := lt_of_lt_of_le (Real.exp_pos _) hE
  have hlog : Real.exp 64 ≤ Real.log E := (Real.le_log_iff_exp_le he).mpr hE
  have hlogpos : 0 < Real.log E := lt_of_lt_of_le (Real.exp_pos _) hlog
  have hll : 64 ≤ Real.log (Real.log E) := (Real.le_log_iff_exp_le hlogpos).mpr hlog
  have hE1 : 1 < E := (Real.log_pos_iff he.le).mp hlogpos
  have hEX : E ≤ X := by
    have hp : E ≤ 8 * Real.pi * E := by nlinarith [Real.pi_gt_three, mul_pos he (show 0 < Real.pi - 1 by linarith [Real.pi_gt_three])]
    dsimp [X]
    nlinarith [mul_nonneg (show 0 ≤ 8 * Real.pi * E by positivity) (show 0 ≤ 8 * Real.pi * E - 1 by linarith)]
  have hX : 1 < X := hE1.trans_le hEX
  have h2log : Real.log 2 ≤ 1 := by simpa only [show (2:ℝ)-1=1 by norm_num, show (32:ℝ)-1=31 by norm_num] using Real.log_le_sub_one_of_pos (show (0:ℝ)<2 by norm_num)
  have h32log : Real.log 32 ≤ 31 := by simpa only [show (2:ℝ)-1=1 by norm_num, show (32:ℝ)-1=31 by norm_num] using Real.log_le_sub_one_of_pos (show (0:ℝ)<32 by norm_num)
  have hext : 32 * (2:ℝ)^(S:ℝ) ≤ Real.log E := by
    rw [Real.rpow_def_of_pos (by norm_num), ← Real.exp_log (show (0:ℝ)<32 by norm_num), ← Real.exp_add]
    apply (Real.le_log_iff_exp_le hlogpos).mp
    nlinarith [mul_le_mul_of_nonneg_right h2log (Nat.cast_nonneg S)]
  have hscale : 32 * (2:ℝ)^(S:ℝ) ≤ Real.log X :=
    hext.trans (Real.log_le_log he hEX)
  have htw : 0 < (2:ℝ)^(S:ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have haux : (S:ℝ) ≤ Real.logb 2 (Real.logb 2 X) := by
    apply (Real.le_logb_iff_rpow_le (by norm_num : (1:ℝ)<2) (Real.logb_pos (by norm_num) hX)).mpr
    rw [Real.logb, le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))]
    nlinarith [mul_le_mul_of_nonneg_left h2log htw.le]
  have hpow : X ^ (-(2:ℝ)^(-(S:ℝ))) ≤ Real.exp (-32) := by
    rw [Real.rpow_def_of_pos (by linarith : 0 < X), Real.rpow_neg (by norm_num : (0:ℝ)≤2)]
    apply Real.exp_le_exp.mpr
    rw [mul_neg, ← div_eq_mul_inv]
    have hh := (le_div_iff₀ htw).mpr hscale
    linarith
  have hlarge : (2:ℝ)^32 ≤ Real.exp 32 := by
    calc
      _ ≤ (Real.exp 1)^32 := pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp (1:ℝ)]) _
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hsmall : Real.exp (-32) ≤ 1/(2:ℝ)^32 := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (by positivity) hlarge
  exact (lemma_6_4 X hX S haux).trans (by nlinarith [hpow.trans hsmall])

theorem solution :
    ∃ c E₀ : ℝ, 0 < c ∧ 1 < E₀ ∧
      ∀ lam : ℝ, 1 < lam → E₀ ≤ energy lam →
      ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
      ∀ (T : ℕ) (P : GaussProtocol T) (S : ℕ),
        CopiesLe lam P S → (2 / 3 : ℝ≥0∞) ≤ succProb lam ε P →
        c * Real.log (Real.log (energy lam)) ≤ S := by
  have hbig : 4 ≤ Real.exp (Real.exp 64) := by
    linarith [Real.add_one_le_exp (64:ℝ), Real.add_one_le_exp (Real.exp 64)]
  refine ⟨1/4, Real.exp (Real.exp 64), by norm_num, by linarith, ?_⟩
  intro lam hl he ε hε hε2 T P S hcap hsucc
  by_contra! hn
  have hE4 := hbig.trans he
  have hE : 1 < energy lam := by linarith
  have hi := small_iter (energy lam) he S (by linarith)
  have hg := (eq_18 P lam hl S hcap).trans (ENNReal.ofReal_le_ofReal hi)
  have hroot : (expG lam P) ^ (1/2 : ℝ) ≤ ENNReal.ofReal (1/1024) := by
    calc
      _ ≤ ENNReal.ofReal ((1/1024 : ℝ)^2) ^ (1/2 : ℝ) := ENNReal.rpow_le_rpow hg (by norm_num)
      _ = _ := by rw [ENNReal.ofReal_pow (by norm_num), ← ENNReal.rpow_natCast_mul]; norm_num
  obtain ⟨hp,hq⟩ := eq_14 P lam ε hl hE hε hε2
  have hf := hsucc.trans (hp.trans hq)
  have hr : (2/3 : ℝ≥0∞) ≤ ENNReal.ofReal (2*ε/energy lam) +
      ENNReal.ofReal (16*Real.pi^2*ε) * ENNReal.ofReal (1/1024) :=
    hf.trans (by gcongr)
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)] at hr
  have heq : (2/3:ℝ≥0∞) = ENNReal.ofReal (2/3) := by rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num
  rw [heq, ENNReal.ofReal_le_ofReal_iff (by positivity)] at hr
  have hb1 : 2*ε/energy lam ≤ 1/4 := (div_le_iff₀ (by linarith)).mpr (by linarith)
  have hb2 : Real.pi^2 ≤ 16 := by nlinarith [mul_nonneg (show 0 ≤ 4 - Real.pi by linarith [Real.pi_lt_four]) (show 0 ≤ 4 + Real.pi by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right hb2 hε.le]
