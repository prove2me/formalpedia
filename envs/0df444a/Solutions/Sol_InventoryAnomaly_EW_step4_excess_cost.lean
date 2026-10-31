-- Prove2me | solution 1 for InventoryAnomaly.EW.step4_excess_cost
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T07:58:58.900222+00:00
-- url     : https://prove2.me/submissions/8c6670dc-12cf-4d8d-a44a-658118fd6887

import Mathlib
import Definitions.Def_InventoryAnomaly_EW_Model

open MeasureTheory ProbabilityTheory
open scoped NNReal
open InventoryAnomaly.EW

theorem solution {d : ℕ} (I : Instance d)
    (hc : ∀ i j, 0 ≤ I.c0 i j ∧ 0 ≤ I.c1 i j)
    (svdr : Matrix (Fin I.n) (Fin I.m) ℝ → Matrix (Fin I.n) (Fin I.m) ℝ)
    (θhat : I.Obs → EuclideanSpace ℝ (Fin (d + 1))) (x : I.Obs) :
    let a := fun i j => -I.c1 i j + (I.c0 i j + I.c1 i j) * I.fhat svdr θhat x i j
    let b := fun i j => -I.c1 i j + (I.c0 i j + I.c1 i j) * I.fstar x i j
    I.costEW svdr θhat x - I.costStar x =
        (1 / ((I.omega x).card : ℝ)) * ∑ ij ∈ I.omega x,
          ((if a ij.1 ij.2 ≤ 0 then 1 else 0) - (if b ij.1 ij.2 ≤ 0 then 1 else 0)) * b ij.1 ij.2 ∧
      I.costEW svdr θhat x - I.costStar x ≤
        (1 / ((I.omega x).card : ℝ)) * ∑ ij ∈ I.omega x, |a ij.1 ij.2 - b ij.1 ij.2| := by
  intro a b
  -- the rule at an estimate `f` is `a ≤ 0` form
  have key : ∀ (c0 c1 f fs : ℝ), 0 ≤ c0 → 0 ≤ c1 →
      ((if decide (f ≤ c1 / (c0 + c1)) = true then c0 * fs else c1 * (1 - fs)) -
        (if decide (fs ≤ c1 / (c0 + c1)) = true then c0 * fs else c1 * (1 - fs))) =
      ((if -c1 + (c0 + c1) * f ≤ 0 then 1 else 0) - (if -c1 + (c0 + c1) * fs ≤ 0 then 1 else 0))
        * (-c1 + (c0 + c1) * fs) := by
    intro c0 c1 f fs h0 h1
    rcases eq_or_lt_of_le (add_nonneg h0 h1) with h | h
    · have e0 : c0 = 0 := by linarith
      have e1 : c1 = 0 := by linarith
      subst e0; subst e1; simp
    · have iff : ∀ g : ℝ, (g ≤ c1 / (c0 + c1)) ↔ (-c1 + (c0 + c1) * g ≤ 0) := by
        intro g; rw [le_div_iff₀ h]; constructor <;> intro hh <;> linarith
      simp only [decide_eq_true_eq, iff]
      split_ifs <;> ring
  have hEq : I.costEW svdr θhat x - I.costStar x =
      (1 / ((I.omega x).card : ℝ)) * ∑ ij ∈ I.omega x,
          ((if a ij.1 ij.2 ≤ 0 then 1 else 0) - (if b ij.1 ij.2 ≤ 0 then 1 else 0)) * b ij.1 ij.2 := by
    unfold Instance.costEW Instance.costStar Instance.cost Instance.rule
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun ij _ => ?_
    exact key _ _ _ _ (hc _ _).1 (hc _ _).2
  refine ⟨hEq, ?_⟩
  rw [hEq]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro ij _
  generalize a ij.1 ij.2 = u
  generalize b ij.1 ij.2 = v
  split_ifs with h1 h2 h2
  · simp
  · rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
  · rw [abs_of_nonneg (by linarith)]; linarith
  · simp
