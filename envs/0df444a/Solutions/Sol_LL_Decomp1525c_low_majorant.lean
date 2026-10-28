-- Prove2me | solution 1 for LL_Decomp1525c.low_majorant
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T17:32:06.702024+00:00
-- url     : https://prove2.me/submissions/2d8468fb-9cbc-4d29-9142-809b5f70fba1

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

lemma zfacts {x : ℝ} (hx : 10 ^ 52 ≤ x) : ∃ z : ℝ, 3 ≤ z ∧ z ≤ x / 2 ∧
    Real.log z = 23 / 26 * Real.log x ∧ z * Real.log x ≤ 3 / 1000 * x := by
  obtain ⟨q, hq, hxq, hL, hLq⟩ := qfacts hx
  have hq0 : 0 < q := by linarith
  refine ⟨q ^ 23, ?_, ?_, ?_, ?_⟩
  · have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 100) hq 23; norm_num at this ⊢; linarith
  · have h3 : (2:ℝ) ≤ q ^ 3 := by
      have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 100) hq 3; norm_num at this ⊢; linarith
    have h23 : 0 < q ^ 23 := by positivity
    rw [hxq, show q ^ 26 = q ^ 23 * q ^ 3 by ring]; nlinarith
  · rw [Real.log_pow, hL]; push_cast; ring
  · have h24 : 0 < q ^ 24 := by positivity
    have h2 : (10000:ℝ) ≤ q ^ 2 := by nlinarith
    have e : q ^ 23 * Real.log x ≤ q ^ 23 * (26 * q) :=
      mul_le_mul_of_nonneg_left hLq (by positivity)
    have e2 : q ^ 23 * (26 * q) = 26 * q ^ 24 := by ring
    have e3 : x = q ^ 24 * q ^ 2 := by rw [hxq]; ring
    have e4 := mul_le_mul_of_nonneg_left h2 h24.le
    rw [e3] at e ⊢
    nlinarith

lemma low_maj (x : ℝ) (hx : 10 ^ 52 ≤ x) :
    ∫ u in (3 : ℝ)..x, (x / (40 * Real.log x)
      + max (x - u) 2 / (40 * Real.log (max (x - u) 2)) + 678412) / Real.log u
      ≤ x ^ 2 / (20 * Real.log x ^ 2) := by
  obtain ⟨hL, hLx⟩ := Lfacts hx
  obtain ⟨z, hz3, hzx, hlz, hzL⟩ := zfacts hx
  set L := Real.log x with hLdef
  have hL0 : 0 < L := by linarith
  have hx0 : 0 < x := by linarith
  set L2 := Real.log (x / 2) with hL2def
  have hL2 : L2 = L - Real.log 2 := by rw [hL2def, Real.log_div hx0.ne' (by norm_num)]
  have hL2' : 99 / 100 * L ≤ L2 := by rw [hL2]; linarith [Real.log_two_lt_d9]
  have hL20 : 0 < L2 := by linarith
  set A := x / (40 * L) with hA
  have hA0 : 0 ≤ A := by positivity
  set B := fun u : ℝ => max (x - u) 2 / (40 * Real.log (max (x - u) 2)) with hB
  have hg : Continuous (fun u => max (x - u) 2) := by fun_prop
  have hh : Continuous (fun u => x / (40 * L) + max (x - u) 2 / (40 * Real.log (max (x - u) 2))
      + 678412) := (continuous_const.add (cont_glog hg (fun u => le_max_right _ _))).add
        continuous_const
  have hcont : ContinuousOn (fun u => (x / (40 * L) + max (x - u) 2 /
      (40 * Real.log (max (x - u) 2)) + 678412) / Real.log u) (Set.Icc 3 x) :=
    cont_div_log hh (by norm_num)
  have hB0 : ∀ u, 0 ≤ max (x - u) 2 / (40 * Real.log (max (x - u) 2)) := by
    intro u
    have : 0 < Real.log (max (x - u) 2) := Real.log_pos (by linarith [le_max_right (x - u) 2])
    have : 0 ≤ max (x - u) 2 := le_trans (by norm_num) (le_max_right _ _)
    positivity
  have hBle : ∀ u t, 3 ≤ u → x - u ≤ t → 16 ≤ t →
      max (x - u) 2 / (40 * Real.log (max (x - u) 2)) ≤ t / (40 * Real.log t) := by
    intro u t hu hut ht
    have hd := dl_le (le_max_right (x - u) 2) (max_le hut (by linarith)) ht
    rw [div_mul_eq_div_div_swap, div_mul_eq_div_div_swap]
    exact div_le_div_of_nonneg_right hd (by norm_num)
  -- integrability
  have hI : ∀ a b, 3 ≤ a → a ≤ b → b ≤ x → IntervalIntegrable (fun u => (x / (40 * L) +
      max (x - u) 2 / (40 * Real.log (max (x - u) 2)) + 678412) / Real.log u) volume a b :=
    fun a b ha hab hb => (hcont.mono (Set.Icc_subset_Icc ha hb)).intervalIntegrable_of_Icc hab
  have hzx' : z ≤ x := by linarith
  rw [← intervalIntegral.integral_add_adjacent_intervals (hI 3 z le_rfl hz3 hzx')
    (hI z x hz3 hzx' le_rfl),
    ← intervalIntegral.integral_add_adjacent_intervals (hI z (x / 2) hz3 hzx (by linarith))
    (hI (x / 2) x (by linarith) (by linarith) le_rfl)]
  -- piece 1
  have p1 := piece (c := 2 * A + 678412) hz3 (hcont.mono (Set.Icc_subset_Icc le_rfl hzx')) (by
    intro u hu
    have hlu : 1 ≤ Real.log u := le_trans log3 (Real.log_le_log (by norm_num) hu.1)
    have hb := hBle u x hu.1 (by linarith [hu.1]) (by linarith)
    have hb0 := hB0 u
    rw [div_le_iff₀ (by linarith)]
    nlinarith)
  -- piece 2
  have hlz0 : 0 < Real.log z := by rw [hlz]; positivity
  have p2 := piece (c := (2 * A + 678412) / Real.log z) hzx
    (hcont.mono (Set.Icc_subset_Icc hz3 (by linarith))) (by
    intro u hu
    have hlu : Real.log z ≤ Real.log u := Real.log_le_log (by linarith) hu.1
    have hb := hBle u x (by linarith [hu.1]) (by linarith [hu.1]) (by linarith)
    have hb0 := hB0 u
    calc _ ≤ (x / (40 * L) + max (x - u) 2 / (40 * Real.log (max (x - u) 2)) + 678412) /
          Real.log z := div_le_div_of_nonneg_left (by linarith) hlz0 hlu
      _ ≤ _ := div_le_div_of_nonneg_right (by linarith) hlz0.le)
  -- piece 3
  have p3 := piece (a := x / 2) (b := x) (c := (A + (x / 2) / (40 * L2) + 678412) / L2) (by linarith)
    (hcont.mono (Set.Icc_subset_Icc (by linarith) le_rfl)) (by
    intro u hu
    have hlu : L2 ≤ Real.log u := Real.log_le_log (by linarith) hu.1
    have hb := hBle u (x / 2) (by linarith [hu.1]) (by linarith [hu.1]) (by linarith)
    have hb0 := hB0 u
    calc _ ≤ (x / (40 * L) + max (x - u) 2 / (40 * Real.log (max (x - u) 2)) + 678412) /
          L2 := div_le_div_of_nonneg_left (by linarith) hL20 hlu
      _ ≤ _ := div_le_div_of_nonneg_right (by linarith) hL20.le)
  -- arithmetic
  set w := x / L with hw
  have hw0 : 10 ^ 10 ≤ w := by rw [hw, le_div_iff₀ hL0]; linarith
  have hAw : 2 * A = w / 20 := by rw [hA, hw]; field_simp; ring
  have hwL : w * L = x := by rw [hw]; field_simp
  have hzw : z ≤ 3 / 1000 * w := by
    refine le_of_mul_le_mul_right ?_ hL0
    nlinarith
  have q1 : (2 * A + 678412) * (z - 3) ≤ (w / 20 + 678412) * (3 / 1000 * w) := by
    rw [hAw]; exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have q2 : (2 * A + 678412) / Real.log z * (x / 2 - z) ≤ (w / 20 + 678412) * (13 / 23 * w) := by
    calc (2 * A + 678412) / Real.log z * (x / 2 - z) ≤ (2 * A + 678412) / Real.log z * (x / 2) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = (w / 20 + 678412) * (13 / 23 * w) := by
          rw [hAw, hlz, hw]; field_simp; ring
  set v := (x / 2) / L2 with hv
  have hvw : v ≤ w / (198 / 100) := by
    have hw0' : 0 ≤ w := by positivity
    rw [hv, div_le_iff₀ hL20]
    nlinarith
  have hv0 : 0 ≤ v := by positivity
  have q3e : (A + (x / 2) / (40 * L2) + 678412) / L2 * (x - x / 2) =
      (w / 40 + v / 40 + 678412) * v := by
    rw [hA, hv, hw]; field_simp; ring
  have q3 : (w / 40 + v / 40 + 678412) * v ≤
      (w / 40 + (w / (198 / 100)) / 40 + 678412) * (w / (198 / 100)) := by
    gcongr
  have he : x ^ 2 / (20 * L ^ 2) = w ^ 2 / 20 := by rw [hw]; field_simp
  rw [he]
  have hww := mul_le_mul_of_nonneg_left hw0 (by positivity : (0:ℝ) ≤ w)
  nlinarith

end S218LLM

theorem solution (x : ℝ) (hx : 10 ^ 52 ≤ x) :
    ∫ u in (3 : ℝ)..x, (x / (40 * Real.log x)
      + max (x - u) 2 / (40 * Real.log (max (x - u) 2)) + 678412) / Real.log u
      ≤ x ^ 2 / (20 * Real.log x ^ 2) :=
  S218LLM.low_maj x hx
