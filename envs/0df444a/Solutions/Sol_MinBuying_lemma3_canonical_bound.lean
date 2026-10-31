-- Prove2me | solution 1 for MinBuying.lemma3_canonical_bound
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T17:19:11.492516+00:00
-- url     : https://prove2.me/submissions/fb28b901-0aec-481f-b9e3-90473afe584d

import Theorems.Thm_MinBuying_canonical_revenue_bridge
import Theorems.Thm_MinBuying_budget_characterization
import Theorems.Thm_MinBuying_critical_ratio_characterization
import Theorems.Thm_MinBuying_continuous_dominates_step

open Set MeasureTheory
open scoped BigOperators

noncomputable section
open MinBuying

private lemma log_chord (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x * Real.log (1 + a) ≤ Real.log (1 + a * x) := by
  have h := strictConcaveOn_log_Ioi.concaveOn.2
    (show (1 + a : ℝ) ∈ Ioi 0 by change 0 < 1 + a; linarith)
    (show (1 : ℝ) ∈ Ioi 0 by norm_num)
    hx0 (show 0 ≤ 1 - x by linarith) (show x + (1 - x) = 1 by ring)
  simp only [smul_eq_mul, Real.log_one, mul_zero, add_zero] at h
  convert h using 1 <;> congr 1 <;> ring

private lemma rejection_lower (p q : ℝ) (hp : 0 < p)
    (h : p * (1 - p / (p + 1) * q) ≤ 1) : 1 - (1 / p) ^ 2 ≤ q := by
  have hp1 : 0 < p + 1 := by linarith
  have hh := mul_le_mul_of_nonneg_right h hp1.le
  have hh' : p * (p + 1) - p ^ 2 * q ≤ p + 1 := by
    convert! hh using 1 <;> try field_simp <;> ring
  apply (le_of_mul_le_mul_left ?_ (sq_pos_of_pos hp))
  convert! (show p ^ 2 - 1 ≤ p ^ 2 * q by nlinarith [hh']) using 1 <;>
    try field_simp <;> ring

private lemma canonical_budget (I : CanonicalInstance)
    (hU : ∀ p : ℝ, 0 ≤ p → canonicalUniformRevenueAt I p ≤ 1) (k : Fin I.count) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin I.count => i ≤ k), Real.log (1 + I.a i)) ≤
      canonicalBudget (1 / I.cap k) := by
  let p := I.cap k
  let x := 1 / p
  let s := Finset.univ.filter (fun i : Fin I.count => i ≤ k)
  let Q := ∏ i ∈ s, p / (p + I.a i)
  have hp : 1 < p := I.cap_one_lt k
  have hp0 : 0 < p := by linarith
  have hx0 : 0 < x := one_div_pos.mpr hp0
  have hx1 : x < 1 := (div_lt_one hp0).mpr hp
  have hterm : triangularReject 1 I.terminalCap p = p / (p + 1) := by
    rw [triangularReject, if_neg (not_le_of_gt hp0), if_pos]
    exact (I.cap_lt_terminal k).le
  have hrejs (i : Fin I.count) :
      triangularReject (I.a i) (I.cap i) p = if i ≤ k then p / (p + I.a i) else 1 := by
    rw [triangularReject, if_neg (not_le_of_gt hp0)]
    by_cases hi : i ≤ k
    · rw [if_pos hi, if_pos (I.caps_decreasing.antitone hi)]
    · rw [if_neg hi, if_neg (not_le_of_gt (I.caps_decreasing (lt_of_not_ge hi)))]
  have hu := hU p hp0.le
  dsimp only [canonicalUniformRevenueAt] at hu
  rw [hterm] at hu
  simp_rw [hrejs] at hu
  simp only [Finset.prod_ite, Finset.prod_const_one, mul_one] at hu
  have hQ : 1 - x ^ 2 ≤ Q := rejection_lower p Q hp0 hu
  have hQpos : 0 < Q := by
    apply Finset.prod_pos
    intro i hi
    exact div_pos hp0 (by linarith [I.a_pos i])
  have harg : 0 < 1 - x ^ 2 := by nlinarith [hx0, hx1]
  have hlog : Real.log (1 - x ^ 2) ≤ Real.log Q := Real.log_le_log harg hQ
  have hQlog : Real.log Q = -(∑ i ∈ s, Real.log (1 + I.a i * x)) := by
    dsimp only [Q]
    rw [Real.log_prod]
    · rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      have heq : p / (p + I.a i) = (1 + I.a i * x)⁻¹ := by
        dsimp [x]
        field_simp
      rw [heq, Real.log_inv]
    · intro i hi
      exact ne_of_gt (div_pos hp0 (by linarith [I.a_pos i]))
  rw [hQlog] at hlog
  have hchord : x * (∑ i ∈ s, Real.log (1 + I.a i)) ≤
      ∑ i ∈ s, Real.log (1 + I.a i * x) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => log_chord (I.a i) x (I.a_pos i) hx0.le hx1.le
  change (∑ i ∈ s, Real.log (1 + I.a i)) ≤ canonicalBudget x
  rw [canonicalBudget, if_neg (ne_of_gt hx0)]
  apply (le_div_iff₀ hx0).mpr
  nlinarith [hlog, hchord]

private lemma flow_consistent (y x : ℝ) (hy : 0 ≤ y) (hyx : y ≤ x) (hx : x < 1) :
    benchmarkFlow y (continuousBenchmark y) x = continuousBenchmark x := by
  have hx0 : 0 ≤ x := hy.trans hyx
  have hS : ContinuousOn (fun t : ℝ => t * budgetSlope t) (Icc 0 x) :=
    continuousOn_id.mul (budget_characterization.2.1.mono
      (fun t ht => ⟨ht.1, ht.2.trans_lt hx⟩))
  have hE : ContinuousOn odeExponent (Icc 0 x) := by
    change ContinuousOn (fun b => ∫ t in (0 : ℝ)..b, t * budgetSlope t) (Icc 0 x)
    simpa only [uIcc_of_le hx0] using
      (intervalIntegral.continuousOn_primitive_interval'
        (hS.intervalIntegrable_of_Icc hx0) (left_mem_uIcc : (0 : ℝ) ∈ Set.uIcc 0 x))
  have hJc : ContinuousOn (fun t => budgetSlope t * Real.exp (odeExponent t)) (Icc 0 x) :=
    (budget_characterization.2.1.mono (fun t ht => ⟨ht.1, ht.2.trans_lt hx⟩)).mul hE.rexp
  have hiy : IntervalIntegrable
      (fun t => budgetSlope t * Real.exp (odeExponent t)) volume 0 y :=
    (hJc.mono (Icc_subset_Icc le_rfl hyx)).intervalIntegrable_of_Icc hy
  have hiyx : IntervalIntegrable
      (fun t => budgetSlope t * Real.exp (odeExponent t)) volume y x :=
    (hJc.mono (Icc_subset_Icc hy le_rfl)).intervalIntegrable_of_Icc hyx
  let J := fun t : ℝ => ∫ s in (0 : ℝ)..t, budgetSlope s * Real.exp (odeExponent s)
  have hJ : (∫ t in y..x, budgetSlope t * Real.exp (odeExponent t)) = J x - J y := by
    have h := intervalIntegral.integral_add_adjacent_intervals hiy hiyx
    dsimp [J]
    linarith
  have hscale : (∫ t in y..x, budgetSlope t * Real.exp (odeExponent t - odeExponent y)) =
      Real.exp (-odeExponent y) * (J x - J y) := by
    have heq : (fun t => budgetSlope t * Real.exp (odeExponent t - odeExponent y)) =
        (fun t => Real.exp (-odeExponent y) * (budgetSlope t * Real.exp (odeExponent t))) := by
      funext t
      rw [sub_eq_add_neg, Real.exp_add]
      ring
    rw [heq, intervalIntegral.integral_const_mul, hJ]
  rw [benchmarkFlow, hscale]
  change Real.exp (-(odeExponent x - odeExponent y)) *
    (Real.exp (-odeExponent y) * (1 + J y) + Real.exp (-odeExponent y) * (J x - J y)) =
      Real.exp (-odeExponent x) * (1 + J x)
  simp only [Real.exp_neg, Real.exp_sub]
  field_simp
  <;> ring

private lemma budgeted_fold {α : Type} (a v : α → ℝ) (l : List α)
    (ha : ∀ i ∈ l, 0 < a i) (hv : ∀ i ∈ l, 1 < v i)
    (y C : ℝ) (hy : y ∈ Ico (0 : ℝ) 1) (hC0 : 0 ≤ C)
    (hCc : C ≤ continuousBenchmark y)
    (hB : ∀ (k : ℕ) (hk : k < l.length),
      canonicalBudget y + ((l.take (k + 1)).map (fun i => Real.log (1 + a i))).sum ≤
        canonicalBudget (1 / v l[k])) :
    l.foldl (fun c i => continuationStep (a i) (v i) c) C ≤ 1 / criticalRatio := by
  induction l generalizing y C with
  | nil => simpa using hCc.trans ((critical_ratio_characterization.2.2.2.1 y hy).2)
  | cons i l ih =>
    have hai : 0 < a i := ha i (by simp)
    have hvi : 1 < v i := hv i (by simp)
    have hA0 : 0 ≤ canonicalBudget y := by
      have h := budget_characterization.2.2.2.1.monotoneOn
        (show (0 : ℝ) ∈ Ico 0 1 by norm_num) hy hy.1
      simpa only [budget_characterization.1] using h
    have hlog : 0 < Real.log (1 + a i) := Real.log_pos (by linarith)
    obtain ⟨y', hy', huniq⟩ := budget_characterization.2.2.2.2
      (canonicalBudget y + Real.log (1 + a i)) (by linarith)
    have hyy' : y < y' := by
      by_contra h
      have hle := budget_characterization.2.2.2.1.monotoneOn hy'.1 hy (le_of_not_gt h)
      linarith [hy'.2]
    have hx0 : 0 < 1 / v i := one_div_pos.mpr (by linarith)
    have hx1 : 1 / v i < 1 := (div_lt_one (by linarith : 0 < v i)).mpr hvi
    have hb0 := hB 0 (by simp)
    simp only [zero_add, List.take_succ_cons, List.take_zero, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, add_zero, List.getElem_cons_zero] at hb0
    have hyv : y' ≤ 1 / v i := by
      by_contra h
      have hlt := budget_characterization.2.2.2.1 ⟨hx0.le, hx1⟩ hy'.1 (lt_of_not_ge h)
      linarith [hy'.2]
    have haeq : Real.exp (canonicalBudget y' - canonicalBudget y) - 1 = a i := by
      rw [hy'.2, add_sub_cancel_left, Real.exp_log (by linarith : 0 < 1 + a i)]
      ring
    have hc1 := (critical_ratio_characterization.2.2.2.1 y hy).1
    have hcnew : continuationStep (a i) (v i) C ≤ continuousBenchmark y' := by
      have hden : 0 < 1 + a i / v i := by positivity
      have hdeny : 0 < 1 + y' * a i := by nlinarith [hy'.1.1, hai]
      calc
        continuationStep (a i) (v i) C ≤ (a i + continuousBenchmark y) / (1 + a i / v i) := by
          exact div_le_div_of_nonneg_right (by linarith) hden.le
        _ ≤ (a i + continuousBenchmark y) / (1 + y' * a i) := by
          apply div_le_div_of_nonneg_left (by linarith) hdeny
          have h := mul_le_mul_of_nonneg_left hyv hai.le
          simp only [mul_one_div] at h
          nlinarith [h]
        _ ≤ benchmarkFlow y (continuousBenchmark y) y' := by
          simpa only [haeq] using continuous_dominates_step y (continuousBenchmark y) y'
            hy.1 hyy'.le hy'.1.2 hc1
        _ = continuousBenchmark y' := flow_consistent y y' hy.1 hyy'.le hy'.1.2
    have hnew0 : 0 ≤ continuationStep (a i) (v i) C := by
      unfold continuationStep
      positivity
    simp only [List.foldl_cons]
    apply ih (fun j hj => ha j (by simp [hj])) (fun j hj => hv j (by simp [hj]))
      y' _ hy'.1 hnew0 hcnew
    intro k hk
    have h := hB (k + 1) (by simpa using Nat.succ_lt_succ hk)
    simp only [List.take_succ_cons, List.map_cons, List.sum_cons,
      List.getElem_cons_succ] at h
    rw [hy'.2]
    linarith [h]

theorem solution (I : CanonicalInstance)
    (hUP : UPRevenue (canonicalLaw I) ≤ 1) :
    Revenue (canonicalLaw I) (canonicalPrices I) ≤ 1 / criticalRatio := by
  have hb := canonical_revenue_bridge I
  have hU : ∀ p : ℝ, 0 ≤ p → canonicalUniformRevenueAt I p ≤ 1 := by
    intro p hp
    rw [← hb.2.2.2 p hp]
    exact (le_csSup hb.2.1.2.1 (show uniformRevenue (canonicalLaw I) p ∈
      uniformValues (canonicalLaw I) from ⟨p, hp, rfl⟩)).trans hUP
  have hB : ∀ (k : ℕ) (hk : k < (List.finRange I.count).length),
      canonicalBudget 0 + (((List.finRange I.count).take (k + 1)).map
        (fun i => Real.log (1 + I.a i))).sum ≤
      canonicalBudget (1 / I.cap (List.finRange I.count)[k]) := by
    intro k hk
    have hk' : k < I.count := by simpa using hk
    have hset : ((List.finRange I.count).take (k + 1)).toFinset =
        Finset.univ.filter (fun i : Fin I.count => i ≤ ⟨k, hk'⟩) := by
      ext i
      simp only [List.mem_toFinset, Finset.mem_filter, Finset.mem_univ, true_and,
        List.mem_take_iff_idxOf_lt (List.mem_finRange i), List.idxOf_finRange,
        Fin.le_def, Nat.lt_succ_iff]
    rw [budget_characterization.1, zero_add,
      ← List.sum_toFinset _ (List.nodup_finRange I.count).take, hset]
    have hget : (List.finRange I.count)[k] = (⟨k, hk'⟩ : Fin I.count) := by
      apply Fin.ext
      simp only [List.getElem_finRange, Fin.coe_cast]
    rw [hget]
    exact canonical_budget I hU ⟨k, hk'⟩
  have hP : 0 < I.terminalCap := zero_lt_one.trans I.terminal_one_lt
  have hC0 : 0 ≤ I.terminalCap / (I.terminalCap + 1) := by positivity
  have hCc : I.terminalCap / (I.terminalCap + 1) ≤ continuousBenchmark 0 := by
    have hc := (critical_ratio_characterization.2.2.2.1 0 (by norm_num)).1
    have hbound : I.terminalCap / (I.terminalCap + 1) ≤ 1 := by
      apply (div_le_one (by positivity : 0 < I.terminalCap + 1)).mpr
      linarith
    exact hbound.trans hc
  have h := budgeted_fold I.a I.cap (List.finRange I.count)
    (fun i _ => I.a_pos i) (fun i _ => I.cap_one_lt i)
    0 (I.terminalCap / (I.terminalCap + 1)) (by norm_num) hC0 hCc hB
  rw [hb.2.2.1]
  simpa [canonicalCapRevenue, canonicalContinuation, List.take_of_length_le] using h
