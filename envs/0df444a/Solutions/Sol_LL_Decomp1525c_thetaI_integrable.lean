-- Prove2me | solution 1 for LL_Decomp1525c.thetaI_integrable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T17:15:27.18772+00:00
-- url     : https://prove2.me/submissions/58dba59c-1478-4ade-a569-c13bf5a537fe

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

end S218LLI

theorem solution (x : ℝ) (hx : 6 ≤ x) :
    IntervalIntegrable (fun u => LL_Decomp1525c.thetaI x u / Real.log u) volume 3 x ∧
    IntervalIntegrable (fun u => LL_Decomp1525c.thetaI x u / Real.log u) volume x (2 * x) :=
  ⟨S218LLI.integrable_on x hx (by norm_num) (by linarith),
    S218LLI.integrable_on x hx (by linarith) (by linarith)⟩
