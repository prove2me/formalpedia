-- Prove2me | solution 1 for LocalRademacher.StarHull.subroot_growth
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T10:27:15.639202+00:00
-- url     : https://prove2.me/submissions/1eb86237-b891-42d8-ad01-ab66af05e6ca

import Mathlib
import Definitions.Def_VarianceRegularization_Localized_LocalizedComplexity
import Definitions.Def_VarianceRegularization_Localized_RobustRisk
import Definitions.Def_LocalRademacher_StarHull_Classes

open MeasureTheory ProbabilityTheory VarianceRegularization.Localized in
theorem solution (ψ : ℝ → ℝ) (hψ : IsSubRoot ψ) (β r : ℝ) (hβ : 1 ≤ β) (hr : 0 ≤ r) :
    ψ (β * r) ≤ Real.sqrt β * ψ r := by
  obtain ⟨hnn, _hmono, hanti⟩ := hψ
  have hsb : 1 ≤ Real.sqrt β := by
    rw [show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hβ
  rcases hr.eq_or_lt with h0 | hpos
  · subst h0
    simp only [mul_zero]
    have := hnn 0 le_rfl
    nlinarith
  · have hβpos : 0 < β := by linarith
    have hbr : 0 < β * r := mul_pos hβpos hpos
    have hle : r ≤ β * r := by nlinarith
    have key := hanti (Set.mem_Ioi.mpr hpos) (Set.mem_Ioi.mpr hbr) hle
    simp only at key
    have hsr : 0 < Real.sqrt r := Real.sqrt_pos.mpr hpos
    have hsβ : 0 < Real.sqrt β := Real.sqrt_pos.mpr hβpos
    rw [Real.sqrt_mul hβpos.le] at key
    rw [div_le_div_iff₀ (mul_pos hsβ hsr) hsr] at key
    have : ψ (β * r) * Real.sqrt r ≤ (Real.sqrt β * ψ r) * Real.sqrt r := by nlinarith
    exact le_of_mul_le_mul_right this hsr
