-- Prove2me | solution 1 for HiddenRebate.Fixed.contract_star_ic
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T15:51:24.686589+00:00
-- url     : https://prove2.me/submissions/fef861f0-7f3b-43d5-a2a4-c7d9547fcecf

import Mathlib
import Definitions.Def_HiddenRebate_Fixed_Model

open HiddenRebate.Fixed

theorem solution (r : ℝ) (hr : 0 ≤ r) :
    Feasible (contractStar r).1 (contractStar r).2 ∧
    IsIC r (contractStar r).1 (contractStar r).2 ∧
    ∀ x : ℝ × ℝ, 0 ≤ x.1 → 0 ≤ x.2 →
      payoff r (contractStar r).1 (contractStar r).2 (quote r x) (quote r x) = r := by
  have hset : {z : ℝ × ℝ | selStar r z = Supplier.S} = {z | z.1 ≤ z.2 - r} := by
    ext z; simp only [selStar, Set.mem_setOf_eq]; split_ifs with h <;> simp [h]
  have hmeas : MeasurableSet {z : ℝ × ℝ | selStar r z = Supplier.S} := by
    rw [hset]; exact measurableSet_le measurable_fst (measurable_snd.sub_const r)
  have htruth : ∀ q : ℝ × ℝ,
      payoff r (contractStar r).1 (contractStar r).2 q q = r := by
    intro q
    simp only [payoff, contractStar, feeStar]
    obtain h | h : selStar r q = .S ∨ selStar r q = .W := by cases selStar r q <;> simp
    all_goals simp [h]
  refine ⟨⟨?_, hmeas, ?_⟩, ?_, fun x _ _ => htruth _⟩
  · intro z; simp only [contractStar, feeStar]; split_ifs <;> linarith
  · show Measurable (feeStar r)
    unfold feeStar
    exact Measurable.ite hmeas measurable_const measurable_const
  · intro x _ _ z
    rw [htruth]
    simp only [payoff, contractStar, feeStar]
    obtain h | h : selStar r z = .S ∨ selStar r z = .W := by cases selStar r z <;> simp
    all_goals simp only [h, reduceCtorEq, if_false, if_true, zero_add, add_zero]
    all_goals split_ifs <;> linarith
