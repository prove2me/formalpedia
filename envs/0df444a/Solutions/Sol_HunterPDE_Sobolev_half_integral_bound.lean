-- Prove2me | solution 1 for HunterPDE.Sobolev.half_integral_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T12:23:20.468034+00:00
-- url     : https://prove2.me/submissions/588176cd-3343-4d1b-82fe-0ac2abfb48e3

import Mathlib

open MeasureTheory in
theorem solution (g : ℝ → ℝ) (hg : Integrable g) (hgc : HasCompactSupport g)
    (hg0 : ∫ t, g t = 0) (x : ℝ) :
    |∫ t in Set.Iic x, g t| ≤ (1 / 2 : ℝ) * ∫ t, |g t| := by
  have hs : MeasurableSet (Set.Iic x) := measurableSet_Iic
  have h1 : (∫ t in Set.Iic x, g t) + ∫ t in (Set.Iic x)ᶜ, g t = ∫ t, g t :=
    integral_add_compl hs hg
  have h2 : (∫ t in Set.Iic x, |g t|) + ∫ t in (Set.Iic x)ᶜ, |g t| = ∫ t, |g t| :=
    integral_add_compl hs hg.abs
  have hA : |∫ t in Set.Iic x, g t| ≤ ∫ t in Set.Iic x, |g t| :=
    abs_integral_le_integral_abs
  have hB : |∫ t in (Set.Iic x)ᶜ, g t| ≤ ∫ t in (Set.Iic x)ᶜ, |g t| :=
    abs_integral_le_integral_abs
  have hBA : ∫ t in (Set.Iic x)ᶜ, g t = -∫ t in Set.Iic x, g t := by linarith
  rw [hBA, abs_neg] at hB
  linarith
