-- Prove2me | solution 1 for LogLogJam.theorem_1_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-26T09:18:56.232797+00:00
-- url     : https://prove2.me/submissions/6a70b379-983b-447c-84f2-19f86af34ff2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_LogLogJam_theorem_6_5
import Theorems.Thm_LogLogJam_lemma_5_4
import Theorems.Thm_LogLogJam_transcript_fisher_copy_cap

open LogLogJam
open scoped ENNReal

private theorem precision_bound {E ε : ℝ} {S : ℕ} (hE : 1 < E)
    (hε : 0 < ε) (hsmall : ε < 1 / 12) {J : ℝ≥0∞}
    (hFisher : J ≤ ENNReal.ofReal ((4*E)^2 * (S : ℝ)))
    (hsuccess : (2/3 : ℝ≥0∞) ≤ ENNReal.ofReal (2*ε/E) *
      (1 + ENNReal.ofReal Real.pi * J ^ (1/2 : ℝ))) :
    (1/4096 : ℝ) * (1 / ε^2) ≤ S := by
  have hEpos : 0 < E := by linarith
  have hnat : 0 ≤ (S : ℝ) := Nat.cast_nonneg _
  have hroot : J ^ (1/2 : ℝ) ≤ ENNReal.ofReal (4*E*Real.sqrt (S : ℝ)) := by
    calc
      _ ≤ (ENNReal.ofReal ((4*E)^2 * (S : ℝ))) ^ (1/2 : ℝ) :=
        ENNReal.rpow_le_rpow hFisher (by norm_num)
      _ = _ := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
          ← Real.sqrt_eq_rpow, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have hreal : (2/3 : ℝ) ≤ (2*ε/E)*(1 + Real.pi*(4*E*Real.sqrt (S : ℝ))) := by
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add (by norm_num) (by positivity),
      ENNReal.ofReal_one, ENNReal.ofReal_mul Real.pi_pos.le]
    norm_num only [ENNReal.ofReal_div_of_pos, ENNReal.ofReal_ofNat] 
    exact hsuccess.trans (by gcongr)
  have hexpand : (2*ε/E)*(1+Real.pi*(4*E*Real.sqrt (S : ℝ))) =
      2*ε/E + 8*Real.pi*(ε*Real.sqrt (S : ℝ)) := by field_simp; ring
  rw [hexpand] at hreal
  have hfirst : 2*ε/E ≤ 2*ε := div_le_self (by positivity) hE.le
  have haux : (1/2 : ℝ) ≤ 32*(ε*Real.sqrt (S : ℝ)) := calc
    _ ≤ 8*Real.pi*(ε*Real.sqrt (S : ℝ)) := by linarith
    _ ≤ _ := by gcongr; linarith [Real.pi_lt_four]
  have hsquare := mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 1/2) haux
  have hsq : 1/4 ≤ 1024*ε^2*(S : ℝ) := by
    calc
      (1/4 : ℝ) = (1/2)*(1/2) := by norm_num
      _ ≤ _ := hsquare
      _ = 1024*ε^2*(Real.sqrt (S : ℝ))^2 := by ring
      _ = _ := by rw [Real.sq_sqrt hnat]
  rw [← mul_div_assoc, mul_one, div_le_iff₀ (sq_pos_of_pos hε)]
  nlinarith only [hsq]

theorem solution :
    ∃ c E₀ ε₀ : ℝ, 0 < c ∧ 1 < E₀ ∧ 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧
      ∀ lam : ℝ, 1 < lam → E₀ ≤ energy lam →
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ (T : ℕ) (P : GaussProtocol T) (S : ℕ),
        CopiesLe lam P S → (2 / 3 : ℝ≥0∞) ≤ succProb lam ε P →
        c * (Real.log (Real.log (energy lam)) + 1 / ε ^ 2) ≤ S := by
  obtain ⟨c, E₀, hc, hE₀, hgrowth⟩ := theorem_6_5
  let b : ℝ := min c (1/4096)
  have hb : 0 < b := lt_min hc (by norm_num)
  refine ⟨b/2, E₀, 1/12, by positivity, hE₀, by norm_num, by norm_num, ?_⟩
  intro lam hlam hE ε hε hsmall T P S hS hsuccess
  have hhalf : ε < 1/2 := by linarith
  have hone := hE₀.trans_le hE
  have hlog := hgrowth lam hlam hE ε hε hhalf T P S hS hsuccess
  have hprec := precision_bound hone hε hsmall (transcript_fisher_copy_cap lam hlam P S hS)
    (hsuccess.trans (lemma_5_4 P lam ε hlam hone hε hhalf))
  have hlog' : b * Real.log (Real.log (energy lam)) ≤ S := by
    by_cases hL : 0 ≤ Real.log (Real.log (energy lam))
    · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) hL).trans hlog
    · exact (mul_nonpos_of_nonneg_of_nonpos hb.le (le_of_not_ge hL)).trans (Nat.cast_nonneg _)
  have hprec' : b * (1/ε^2) ≤ S :=
    (mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)).trans hprec
  linarith only [hlog', hprec']
