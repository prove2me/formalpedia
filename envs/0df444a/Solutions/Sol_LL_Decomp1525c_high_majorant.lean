-- Prove2me | solution 1 for LL_Decomp1525c.high_majorant
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T17:31:35.009925+00:00
-- url     : https://prove2.me/submissions/42824278-9911-4e5a-9a14-4b4d93a14e13

import Mathlib
import Definitions.Def_LL_Decomp1525c_P1V
import Definitions.Def_LL_Decomp1525c_thetaI

open MeasureTheory

namespace S218LLM

lemma dl_mono {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (hl : 1 ≤ Real.log s) :
    s / Real.log s ≤ t / Real.log t := by
  have ht : 0 < t := lt_of_lt_of_le hs hst
  have hlt : Real.log s ≤ Real.log t := Real.log_le_log hs hst
  have h1 : Real.log t - Real.log s ≤ t / s - 1 := by
    rw [← Real.log_div ht.ne' hs.ne']; exact Real.log_le_sub_one_of_pos (by positivity)
  have h2 : s * (t / s - 1) = t - s := by field_simp
  have h3 : s * (Real.log t - Real.log s) ≤ t - s := by
    rw [← h2]; exact mul_le_mul_of_nonneg_left h1 hs.le
  have h4 : t - s ≤ (t - s) * Real.log s := by nlinarith
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

lemma log3 : 1 ≤ Real.log 3 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]; linarith [Real.exp_one_lt_d9]

lemma dl_le {s t : ℝ} (hs : 2 ≤ s) (hst : s ≤ t) (ht : 16 ≤ t) :
    s / Real.log s ≤ t / Real.log t := by
  rcases le_or_gt 3 s with h | h
  · exact dl_mono (by linarith) hst (le_trans log3 (Real.log_le_log (by norm_num) h))
  · have hl2 := Real.log_two_gt_d9
    have hl16 : Real.log 16 = 4 * Real.log 2 := by
      rw [show (16:ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
    have hls : Real.log 2 ≤ Real.log s := Real.log_le_log (by norm_num) hs
    have e1 : s / Real.log s ≤ 4 / Real.log 2 := by
      rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith
    have e2 : 4 / Real.log 2 = 16 / Real.log 16 := by
      rw [hl16]; field_simp; norm_num
    have e3 := dl_mono (s := 16) (t := t) (by norm_num) ht (by rw [hl16]; linarith)
    linarith

lemma qfacts {x : ℝ} (hx : 10 ^ 52 ≤ x) :
    ∃ q : ℝ, 100 ≤ q ∧ x = q ^ 26 ∧ Real.log x = 26 * Real.log q ∧ Real.log x ≤ 26 * q := by
  have hx0 : 0 < x := by linarith
  set q := Real.exp (Real.log x / 26) with hq
  have hqx : x = q ^ 26 := by
    rw [hq, ← Real.exp_nat_mul]; push_cast
    rw [show (26:ℝ) * (Real.log x / 26) = Real.log x by ring, Real.exp_log hx0]
  have hq0 : 0 < q := Real.exp_pos _
  have h100 : 100 ≤ q := by
    by_contra hc
    rw [not_le] at hc
    have := pow_lt_pow_left₀ hc hq0.le (n := 26) (by norm_num)
    rw [← hqx] at this; norm_num at this; linarith
  refine ⟨q, h100, hqx, ?_, ?_⟩
  · rw [hqx, Real.log_pow]; norm_num
  · have := Real.add_one_le_exp (Real.log x / 26)
    rw [← hq] at this; linarith

lemma Lfacts {x : ℝ} (hx : 10 ^ 52 ≤ x) :
    100 ≤ Real.log x ∧ 10 ^ 10 * Real.log x ≤ x := by
  obtain ⟨q, hq, hxq, hL, hLq⟩ := qfacts hx
  have hl4 : 4 < Real.log q := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    have : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    have := Real.exp_one_lt_d9
    have h0 := Real.exp_pos 1
    calc Real.exp 1 ^ 4 < 2.7182818286 ^ 4 := by gcongr
      _ < 100 := by norm_num
      _ ≤ q := hq
  refine ⟨by linarith, ?_⟩
  have h25 : (100:ℝ) ^ 25 ≤ q ^ 25 := pow_le_pow_left₀ (by norm_num) hq 25
  have : x = q ^ 25 * q := by rw [hxq]; ring
  nlinarith

lemma piece {f : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Set.Icc a b))
    (hc : ∀ u ∈ Set.Icc a b, f u ≤ c) : ∫ u in a..b, f u ≤ c * (b - a) := by
  have := intervalIntegral.integral_mono_on hab (hf.intervalIntegrable_of_Icc (μ := volume) hab)
    (intervalIntegrable_const (μ := volume) (c := c)) hc
  simpa [intervalIntegral.integral_const, mul_comm] using this

lemma cont_glog {g : ℝ → ℝ} (hg : Continuous g) (h2 : ∀ u, 2 ≤ g u) :
    Continuous (fun u => g u / (40 * Real.log (g u))) := by
  have hl : ∀ u, 0 < Real.log (g u) := fun u => Real.log_pos (by linarith [h2 u])
  exact hg.div (continuous_const.mul (hg.log fun u => ne_of_gt (by linarith [h2 u])))
    fun u => mul_ne_zero (by norm_num) (hl u).ne'

lemma cont_div_log {h : ℝ → ℝ} (hh : Continuous h) {a b : ℝ} (ha : 1 < a) :
    ContinuousOn (fun u => h u / Real.log u) (Set.Icc a b) :=
  hh.continuousOn.div (Real.continuousOn_log.mono fun v hv => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [hv.1])
    fun v hv => (Real.log_pos (by linarith [hv.1])).ne'

lemma high_maj (x : ℝ) (hx : 10 ^ 52 ≤ x) :
    ∫ u in x..(2 * x), (max (min (x - 3) (2 * x - u)) 2 /
        (40 * Real.log (max (min (x - 3) (2 * x - u)) 2)) + 678412) / Real.log u
      ≤ x ^ 2 / (20 * Real.log x ^ 2) := by
  obtain ⟨hL, hLx⟩ := Lfacts hx
  set L := Real.log x with hLdef
  have hL0 : 0 < L := by linarith
  have hg : Continuous (fun u => max (min (x - 3) (2 * x - u)) 2) := by fun_prop
  have hh : Continuous (fun u => max (min (x - 3) (2 * x - u)) 2 /
      (40 * Real.log (max (min (x - 3) (2 * x - u)) 2)) + 678412) :=
    (cont_glog hg (fun u => le_max_right _ _)).add continuous_const
  have hcont := cont_div_log hh (a := x) (b := 2 * x) (by linarith)
  have hp := piece (c := (x / (40 * L) + 678412) / L) (by linarith) hcont (by
    intro u hu
    have hu0 : 0 < u := by linarith [hu.1]
    have hlu : L ≤ Real.log u := Real.log_le_log (by linarith) hu.1
    set M := max (min (x - 3) (2 * x - u)) 2 with hM
    have hM2 : 2 ≤ M := le_max_right _ _
    have hMx : M ≤ x := max_le (le_trans (min_le_left _ _) (by linarith)) (by linarith)
    have hd := dl_le hM2 hMx (by linarith)
    have hlM : 0 < Real.log M := Real.log_pos (by linarith)
    have e1 : M / (40 * Real.log M) ≤ x / (40 * L) := by
      rw [div_mul_eq_div_div_swap, div_mul_eq_div_div_swap]
      exact div_le_div_of_nonneg_right hd (by norm_num)
    have hnum : 0 ≤ M / (40 * Real.log M) + 678412 := by positivity
    calc (M / (40 * Real.log M) + 678412) / Real.log u
        ≤ (M / (40 * Real.log M) + 678412) / L := div_le_div_of_nonneg_left hnum hL0 hlu
      _ ≤ (x / (40 * L) + 678412) / L := div_le_div_of_nonneg_right (by linarith) hL0.le)
  refine le_trans hp ?_
  have hw : 40 * 678412 ≤ x / L := by
    rw [le_div_iff₀ hL0]; nlinarith
  have e1 : (x / (40 * L) + 678412) / L * (2 * x - x) = (x / L) ^ 2 / 40 + 678412 * (x / L) := by
    field_simp; ring
  have e2 : x ^ 2 / (20 * L ^ 2) = (x / L) ^ 2 / 20 := by field_simp
  rw [e1, e2]
  have : 0 ≤ x / L := by positivity
  nlinarith

end S218LLM

theorem solution (x : ℝ) (hx : 10 ^ 52 ≤ x) :
    ∫ u in x..(2 * x), (max (min (x - 3) (2 * x - u)) 2 /
        (40 * Real.log (max (min (x - 3) (2 * x - u)) 2)) + 678412) / Real.log u
      ≤ x ^ 2 / (20 * Real.log x ^ 2) :=
  S218LLM.high_maj x hx
