-- Prove2me | solution 1 for LearnVsOpt.display_6
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T15:10:49.159067+00:00
-- url     : https://prove2.me/submissions/23b94347-f361-4da2-b5c3-eeff382fb898

import Mathlib

namespace LearnVsOptAux

lemma step_mul (a b y : ℝ) :
    ((if y ≤ a then (1:ℝ) else 0) * (if y ≤ b then 1 else 0)) = if y ≤ min a b then 1 else 0 := by
  by_cases ha : y ≤ a <;> by_cases hb : y ≤ b <;> simp [ha, hb]

lemma step_antitone (c : ℝ) : Antitone (fun y : ℝ => if y ≤ c then (1:ℝ) else 0) := by
  intro x y hxy
  by_cases hy : y ≤ c
  · simp [hy, hxy.trans hy]
  · simp only [hy, if_false]; split_ifs <;> norm_num

lemma step_integral (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    (∫ y in (-1 : ℝ)..1, (if y ≤ c then (1:ℝ) else 0)) = 1 + c := by
  have hfun : (fun y : ℝ => if y ≤ c then (1:ℝ) else 0) = (Set.Iic c).indicator 1 := by
    ext y; simp [Set.indicator, Set.mem_Iic]
  rw [intervalIntegral.integral_of_le (by norm_num), hfun,
    MeasureTheory.integral_indicator measurableSet_Iic]
  simp only [Pi.one_apply]
  rw [MeasureTheory.Measure.restrict_restrict measurableSet_Iic, MeasureTheory.integral_const]
  have hset : Set.Iic c ∩ Set.Ioc (-1 : ℝ) 1 = Set.Ioc (-1) c := by
    ext y; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioc]; constructor
    · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1, h2.trans hc1⟩
  rw [MeasureTheory.Measure.real, MeasureTheory.Measure.restrict_apply_univ, hset, Real.volume_Ioc]
  rw [ENNReal.toReal_ofReal (by linarith)]
  simp; ring

lemma inner_formula {m m' : ℕ} (w q : Fin m → ℝ) (w' q' : Fin m' → ℝ)
    (hq : ∀ k, q k ∈ Set.Icc (0 : ℝ) 1) (hq' : ∀ l, q' l ∈ Set.Icc (0 : ℝ) 1) :
    (∫ y in (-1 : ℝ)..1, (∑ k, w k * (if y ≤ q k then 1 else 0)) *
        (∑ l, w' l * (if y ≤ q' l then 1 else 0))) =
      ∑ k, ∑ l, w k * w' l * (1 + min (q k) (q' l)) := by
  have hexp : ∀ y : ℝ, (∑ k, w k * (if y ≤ q k then (1:ℝ) else 0)) *
        (∑ l, w' l * (if y ≤ q' l then 1 else 0)) =
      ∑ k, ∑ l, w k * w' l * (if y ≤ min (q k) (q' l) then 1 else 0) := by
    intro y
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
    rw [← step_mul]; ring
  simp_rw [hexp]
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [intervalIntegral.integral_const_mul, step_integral]
      · exact le_min (hq k).1 (hq' l).1
      · exact (min_le_left _ _).trans (hq k).2
    · intro l _
      exact ((step_antitone _).intervalIntegrable).const_mul _
  · intro k _
    have h := IntervalIntegrable.sum (μ := MeasureTheory.volume) (a := -1) (b := 1) Finset.univ
      (f := fun l (y : ℝ) => w k * w' l * (if y ≤ min (q k) (q' l) then (1:ℝ) else 0))
      (fun l _ => ((step_antitone _).intervalIntegrable).const_mul _)
    rw [Finset.sum_fn] at h
    exact h

end LearnVsOptAux

theorem solution {m m' : ℕ} (w q : Fin m → ℝ) (w' q' : Fin m' → ℝ)
    (hq : ∀ k, q k ∈ Set.Icc (0 : ℝ) 1) (hq' : ∀ l, q' l ∈ Set.Icc (0 : ℝ) 1) :
    (∫ y in (-1 : ℝ)..1, (∑ k, w k * (if y ≤ q k then 1 else 0)) *
        (∑ l, w' l * (if y ≤ q' l then 1 else 0))) =
      ∑ k, ∑ l, w k * w' l * (1 + min (q k) (q' l)) ∧
    (∫ y in (-1 : ℝ)..1, (∑ k, w k * (if y ≤ q k then 1 else 0)) ^ 2) =
      ∑ k, ∑ k', w k * w k' * (1 + min (q k) (q k')) := by
  refine ⟨LearnVsOptAux.inner_formula w q w' q' hq hq', ?_⟩
  simp_rw [sq]
  exact LearnVsOptAux.inner_formula w q w q hq hq
