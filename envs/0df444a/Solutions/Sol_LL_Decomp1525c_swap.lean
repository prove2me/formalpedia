-- Prove2me | solution 1 for LL_Decomp1525c.swap
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T17:15:35.581723+00:00
-- url     : https://prove2.me/submissions/382166b1-fdfa-478b-9289-da17bfe26cf1

import Mathlib
import Definitions.Def_LL_Decomp1525c_P1V
import Definitions.Def_LL_Decomp1525c_thetaI

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

lemma indicator_integral {f : ℝ → ℝ} {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (hac : a ≤ c)
    (hdb : d ≤ b) :
    ∫ v in a..b, (Set.Ioc c d).indicator f v = ∫ v in c..d, f v := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd,
    setIntegral_indicator measurableSet_Ioc,
    Set.inter_eq_right.2 (Set.Ioc_subset_Ioc hac hdb)]

end S218LLI

theorem solution (x : ℝ) (hx : 6 ≤ x) :
    ∑ p ∈ LL_Decomp1525c.P1V x, Real.log p * ∫ u in (x - p)..(2 * x - p), 1 / Real.log u =
      ∫ u in (3 : ℝ)..(2 * x), LL_Decomp1525c.thetaI x u / Real.log u := by
  simp_rw [S218LLI.thetaI_div_eq]
  rw [intervalIntegral.integral_finset_sum (fun p _ =>
    S218LLI.term_integrable _ _ measurableSet_Ioc (by norm_num) (by linarith))]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨h3, hpx⟩ := S218LLI.P1V_bounds hx hp
  rw [S218LLI.indicator_integral (by linarith) (by linarith) (by linarith) (by linarith),
    ← intervalIntegral.integral_const_mul]
  congr 1; funext v; ring
