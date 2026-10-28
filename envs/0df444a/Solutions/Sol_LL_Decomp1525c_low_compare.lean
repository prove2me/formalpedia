-- Prove2me | solution 1 for LL_Decomp1525c.low_compare
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T17:32:41.247997+00:00
-- url     : https://prove2.me/submissions/24cb75cc-5ccd-4b9b-aac6-8056e5cf5a3d

import Mathlib
import Definitions.Def_LL_Decomp1525c_P1V
import Definitions.Def_LL_Decomp1525c_thetaI

open Finset

namespace S218LL

/-- θ splits at a lower threshold `m ≤ y`. -/
lemma theta_split (y m : ℝ) (hm0 : 0 ≤ m) (hmy : m ≤ y) :
    Chebyshev.theta y = Chebyshev.theta m +
      ∑ p ∈ ((Ioc 0 ⌊y⌋₊).filter Nat.Prime).filter (fun p => ¬ p ≤ ⌊m⌋₊), Real.log p := by
  rw [Chebyshev.theta, Chebyshev.theta, ← sum_filter_add_sum_filter_not _ (fun p => p ≤ ⌊m⌋₊)]
  congr 1
  apply sum_congr _ (fun _ _ => rfl)
  ext p
  have := Nat.floor_le_floor (a := m) (b := y) hmy
  simp only [mem_filter, mem_Ioc]
  constructor
  · rintro ⟨⟨⟨h1, _⟩, h3⟩, h4⟩; exact ⟨⟨h1, h4⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨⟨h1, le_trans h2 this⟩, h3⟩, h2⟩

lemma theta_two : Chebyshev.theta 2 = Real.log 2 := by
  rw [Chebyshev.theta, show ⌊(2:ℝ)⌋₊ = 2 by norm_num,
    show (Ioc 0 2).filter Nat.Prime = {2} by decide]
  simp

lemma thetaI_low_eq (x u : ℝ) (hx : 6 ≤ x) (hu3 : 3 ≤ u) (hux : u ≤ x) :
    LL_Decomp1525c.thetaI x u = Chebyshev.theta (x - 3) - Chebyshev.theta (max (x - u) 2) := by
  set m := max (x - u) 2 with hm
  have hm0 : 0 ≤ m := le_trans (by norm_num) (le_max_right _ _)
  have hmy : m ≤ x - 3 := max_le (by linarith) (by linarith)
  rw [theta_split (x - 3) m hm0 hmy, add_sub_cancel_left, LL_Decomp1525c.thetaI,
    LL_Decomp1525c.P1V]
  apply sum_congr _ (fun _ _ => rfl)
  ext p
  have hx3 : (0:ℝ) ≤ x - 3 := by linarith
  simp only [mem_filter, mem_Icc, mem_Ioc, not_le]
  rw [Nat.floor_lt hm0]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, hp⟩, h3, h4⟩
    refine ⟨⟨⟨by omega, h2⟩, hp⟩, max_lt (by linarith) ?_⟩
    exact_mod_cast (show 2 < p by omega)
  · rintro ⟨⟨⟨h1, h2⟩, hp⟩, h3⟩
    have hp2 : (2:ℝ) < p := lt_of_le_of_lt (le_max_right _ _) h3
    have hp3 : 3 ≤ p := by exact_mod_cast (show (2:ℝ) < p from hp2)
    have hpx : (p:ℝ) ≤ x - 3 := (Nat.le_floor_iff hx3).1 h2
    exact ⟨⟨⟨hp3, h2⟩, hp⟩, by linarith [le_max_left (x - u) 2], by linarith⟩

lemma theta_err (h215 : ∀ y : ℝ, 678407 ≤ y → |Chebyshev.theta y - y| < y / (40 * Real.log y))
    (m : ℝ) (hm2 : 2 ≤ m) :
    |Chebyshev.theta m - m| ≤ m / (40 * Real.log m) + 678407 := by
  have hlog : 0 < Real.log m := Real.log_pos (by linarith)
  have hq : 0 ≤ m / (40 * Real.log m) := by positivity
  rcases le_or_gt 678407 m with h | h
  · linarith [h215 m h]
  · have h4 : Real.log 4 < 2 := by
      have : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      rw [this]; linarith [Real.log_two_lt_d9]
    have hup := Chebyshev.theta_le_log4_mul_x (x := m) (by linarith)
    have hnn := Chebyshev.theta_nonneg m
    rw [abs_le]
    constructor <;> nlinarith

lemma div_log_mono {x : ℝ} (hx : 10 ^ 52 ≤ x) :
    (x - 3) / (40 * Real.log (x - 3)) ≤ x / (40 * Real.log x) := by
  have hx3 : 0 < x - 3 := by linarith
  have hl3 : 0 < Real.log (x - 3) := Real.log_pos (by linarith)
  have hlx : 2 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have : Real.exp 2 < 8 := by
      have := Real.exp_one_lt_d9
      calc Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
        _ < 8 := by nlinarith [Real.exp_pos 1]
    linarith
  have hdiff : Real.log x - Real.log (x - 3) ≤ 3 / (x - 3) := by
    rw [← Real.log_div (by linarith) hx3.ne']
    have := Real.log_le_sub_one_of_pos (x := x / (x - 3)) (by positivity)
    have he : x / (x - 3) - 1 = 3 / (x - 3) := by field_simp; ring
    linarith
  have h3 : 3 / (x - 3) * x ≤ 6 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hx3]; nlinarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : (x - 3) * Real.log x ≤ x * Real.log (x - 3) := by
    have : x * (Real.log x - Real.log (x - 3)) ≤ 6 := by
      calc x * (Real.log x - Real.log (x - 3)) ≤ x * (3 / (x - 3)) :=
            mul_le_mul_of_nonneg_left hdiff (by linarith)
        _ ≤ 6 := by linarith [h3]
    nlinarith
  nlinarith

end S218LL

theorem S218LLP.pw
    (h215 : ∀ y : ℝ, 678407 ≤ y → |Chebyshev.theta y - y| < y / (40 * Real.log y))
    (x u : ℝ) (hx : 10 ^ 52 ≤ x) (hu3 : 3 ≤ u) (hux : u ≤ x) :
    |LL_Decomp1525c.thetaI x u - u| ≤ x / (40 * Real.log x)
      + max (x - u) 2 / (40 * Real.log (max (x - u) 2)) + 678412 := by
  rw [S218LL.thetaI_low_eq x u (by linarith) hu3 hux]
  have e1 := abs_le.1 (h215 (x - 3) (by linarith)).le
  have e1' := S218LL.div_log_mono hx
  have e2 := abs_le.1 (S218LL.theta_err h215 (max (x - u) 2) (le_max_right _ _))
  have hm1 : x - u ≤ max (x - u) 2 := le_max_left _ _
  have hm2 : max (x - u) 2 ≤ x - u + 2 := max_le (by linarith) (by linarith)
  rw [abs_le]
  constructor <;> linarith


open Finset MeasureTheory

namespace S218LLI

lemma thetaI_div_eq (x u : ℝ) :
    LL_Decomp1525c.thetaI x u / Real.log u =
      ∑ p ∈ LL_Decomp1525c.P1V x,
        (Set.Ioc (x - p) (2 * x - p)).indicator (fun v => Real.log p / Real.log v) u := by
  rw [LL_Decomp1525c.thetaI, sum_filter, sum_div]
  apply sum_congr rfl
  intro p _
  by_cases h : x - p < u ∧ u ≤ 2 * x - p
  · rw [if_pos h, Set.indicator_of_mem (by exact h)]
  · rw [if_neg h, Set.indicator_of_notMem (by exact h), zero_div]

lemma P1V_bounds {x : ℝ} (hx : 6 ≤ x) {p : ℕ} (hp : p ∈ LL_Decomp1525c.P1V x) :
    (3:ℝ) ≤ p ∧ (p:ℝ) ≤ x - 3 := by
  simp only [LL_Decomp1525c.P1V, mem_filter, mem_Icc] at hp
  exact ⟨by exact_mod_cast hp.1.1, (Nat.le_floor_iff (by linarith)).1 hp.1.2⟩

lemma cont_inv_log (c : ℝ) {a b : ℝ} (ha : 1 < a) :
    ContinuousOn (fun v => c / Real.log v) (Set.Icc a b) := by
  apply continuousOn_const.div (Real.continuousOn_log.mono (fun v hv => ?_))
  · intro v hv
    exact ne_of_gt (Real.log_pos (lt_of_lt_of_le ha hv.1))
  · exact ne_of_gt (lt_of_lt_of_le (by linarith) hv.1)

lemma term_integrable (c : ℝ) (s : Set ℝ) (hs : MeasurableSet s) {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    IntervalIntegrable (s.indicator (fun v => c / Real.log v)) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  exact ((cont_inv_log c (b := b) ha).integrableOn_Icc).indicator hs

lemma integrable_on (x : ℝ) (hx : 6 ≤ x) {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun u => LL_Decomp1525c.thetaI x u / Real.log u) volume a b := by
  have : (fun u => LL_Decomp1525c.thetaI x u / Real.log u) =
      ∑ p ∈ LL_Decomp1525c.P1V x,
        (Set.Ioc (x - p) (2 * x - p)).indicator (fun v => Real.log p / Real.log v) := by
    funext u; rw [thetaI_div_eq, Finset.sum_apply]
  rw [this]
  exact IntervalIntegrable.sum _ fun p _ => term_integrable _ _ measurableSet_Ioc ha hab

end S218LLI


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

theorem solution
    (h215 : ∀ y : ℝ, 678407 ≤ y → |Chebyshev.theta y - y| < y / (40 * Real.log y))
    (x : ℝ) (hx : 10 ^ 52 ≤ x) :
    |(∫ u in (3 : ℝ)..x, LL_Decomp1525c.thetaI x u / Real.log u) - ∫ u in (3 : ℝ)..x, u / Real.log u|
      ≤ x ^ 2 / (20 * Real.log x ^ 2) := by
  have hx6 : (6:ℝ) ≤ x := by linarith
  have hf := S218LLI.integrable_on x hx6 (a := 3) (b := x) (by norm_num) (by linarith)
  have hg : IntervalIntegrable (fun u => u / Real.log u) volume 3 x :=
    (S218LLM.cont_div_log continuous_id (a := 3) (b := x) (by norm_num)).intervalIntegrable_of_Icc
      (by linarith)
  have hgm : Continuous (fun u => max (x - u) 2) := by fun_prop
  have hh : Continuous (fun u => x / (40 * Real.log x) + max (x - u) 2 /
      (40 * Real.log (max (x - u) 2)) + 678412) :=
    (continuous_const.add (S218LLM.cont_glog hgm (fun u => le_max_right _ _))).add continuous_const
  have hm : IntervalIntegrable (fun u => (x / (40 * Real.log x) + max (x - u) 2 /
      (40 * Real.log (max (x - u) 2)) + 678412) / Real.log u) volume 3 x :=
    (S218LLM.cont_div_log hh (a := 3) (b := x) (by norm_num)).intervalIntegrable_of_Icc
      (by linarith)
  rw [← intervalIntegral.integral_sub hf hg]
  refine le_trans (intervalIntegral.abs_integral_le_integral_abs (by linarith)) ?_
  refine le_trans ?_ (S218LLM.low_maj x hx)
  apply intervalIntegral.integral_mono_on (by linarith) (hf.sub hg).abs hm
  intro u hu
  have hlu : 0 < Real.log u := Real.log_pos (by linarith [hu.1])
  rw [← sub_div, abs_div, abs_of_pos hlu]
  exact div_le_div_of_nonneg_right (S218LLP.pw h215 x u hx hu.1 hu.2) hlu.le
