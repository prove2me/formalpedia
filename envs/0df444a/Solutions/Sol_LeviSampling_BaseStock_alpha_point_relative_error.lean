-- Prove2me | solution 1 for LeviSampling.BaseStock.alpha_point_relative_error
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:21:42.836987+00:00
-- url     : https://prove2.me/submissions/db1428bd-abde-433f-bade-afd1e73e062c

import Mathlib
import Definitions.Def_LeviSampling_BaseStock_AlphaPoint

open LeviSampling.BaseStock
/-- **Lemma 3.3** (Levi, Roundy & Shmoys 2007, p. 833). Let `f : ℝ → ℝ` be convex with a minimum
at `y*`, and suppose `f(y) ≥ h (y - d)⁺ + b (d - y)⁺` for all `y`, where `h, b > 0`. Let
`0 < ε ≤ 1` and `α = (ε/3) min(b, h)`. If `ŷ` is an `α`-point of `f`, then
`f(ŷ) ≤ (1 + ε) f(y*)`. -/
theorem solution (f : ℝ → ℝ) (hf : ConvexOn ℝ Set.univ f) (ystar : ℝ)
    (hmin : ∀ y, f ystar ≤ f y) (h b d : ℝ) (hh : 0 < h) (hb : 0 < b)
    (hlow : ∀ y, h * max (y - d) 0 + b * max (d - y) 0 ≤ f y)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (yhat : ℝ)
    (hα : IsAlphaPoint f (ε / 3 * min b h) yhat) :
    f yhat ≤ (1 + ε) * f ystar := by
  obtain ⟨r, hr, hsub⟩ := hα
  set m := min b h
  have hm : 0 < m := lt_min hb hh
  have hlow' : ∀ y, m * |y - d| ≤ f y := by
    intro y
    have := hlow y
    rcases le_total y d with hyd | hyd
    · rw [abs_of_nonpos (by linarith)]; rw [max_eq_right (by linarith), max_eq_left (by linarith)] at this
      nlinarith [min_le_left b h]
    · rw [abs_of_nonneg (by linarith)]; rw [max_eq_left (by linarith), max_eq_right (by linarith)] at this
      nlinarith [min_le_right b h]
  have h1 := hsub ystar
  have h2 : -(r * (ystar - yhat)) ≤ ε / 3 * m * |yhat - ystar| := by
    have : |r * (ystar - yhat)| ≤ ε / 3 * m * |yhat - ystar| := by
      rw [abs_mul, abs_sub_comm]; exact mul_le_mul_of_nonneg_right hr (abs_nonneg _)
    linarith [neg_abs_le (r * (ystar - yhat))]
  have h3 : |yhat - ystar| ≤ |yhat - d| + |ystar - d| := by
    calc |yhat - ystar| = |(yhat - d) - (ystar - d)| := by ring_nf
      _ ≤ |yhat - d| + |ystar - d| := abs_sub _ _
  have h4 := hlow' yhat
  have h5 := hlow' ystar
  have hfs : 0 ≤ f ystar := le_trans (mul_nonneg hm.le (abs_nonneg _)) h5
  -- f yhat ≤ f ystar + ε/3 (f yhat + f ystar)
  have key : f yhat ≤ f ystar + ε / 3 * (f yhat + f ystar) := by
    have : ε / 3 * m * |yhat - ystar| ≤ ε / 3 * (f yhat + f ystar) := by
      have : m * |yhat - ystar| ≤ f yhat + f ystar := by nlinarith
      nlinarith
    linarith
  have k2 : (1 - ε / 3) * f yhat ≤ (1 - ε / 3) * ((1 + ε) * f ystar) := by
    nlinarith [mul_nonneg (mul_nonneg hε.le (sub_nonneg.2 hε1)) hfs]
  exact le_of_mul_le_mul_left k2 (by linarith)


