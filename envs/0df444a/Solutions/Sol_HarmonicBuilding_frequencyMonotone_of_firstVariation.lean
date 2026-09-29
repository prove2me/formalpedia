-- Prove2me | solution 1 for HarmonicBuilding.frequencyMonotone_of_firstVariation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T11:30:47.610501+00:00
-- url     : https://prove2.me/submissions/ff35c642-520a-4e63-abc0-4ac39dc5d93f

import Mathlib

theorem solution (r₀ : ℝ) (E I F Ederiv : ℝ → ℝ)
    (hI : ∀ r ∈ Set.Ioo (0:ℝ) r₀, 0 < I r)
    (hIderiv : ∀ r ∈ Set.Ioo (0:ℝ) r₀, HasDerivAt I (I r / r + 2 * E r) r)
    (hEderiv : ∀ r ∈ Set.Ioo (0:ℝ) r₀, HasDerivAt E (Ederiv r) r)
    (hEF : ∀ r ∈ Set.Ioo (0:ℝ) r₀, 2 * F r ≤ Ederiv r)
    (hCS : ∀ r ∈ Set.Ioo (0:ℝ) r₀, E r ^ 2 ≤ I r * F r) :
    MonotoneOn (fun r => r * E r / I r) (Set.Ioo 0 r₀) := by
  have hint : interior (Set.Ioo (0:ℝ) r₀) = Set.Ioo 0 r₀ := interior_Ioo
  -- the frequency has an explicit derivative
  have hN : ∀ r ∈ Set.Ioo (0:ℝ) r₀,
      HasDerivAt (fun s => s * E s / I s)
        (((E r + r * Ederiv r) * I r - (r * E r) * (I r / r + 2 * E r)) / I r ^ 2) r := by
    intro r hr
    have hnum : HasDerivAt (fun s => s * E s) (1 * E r + r * Ederiv r) r :=
      (hasDerivAt_id r).mul (hEderiv r hr)
    have hden := hIderiv r hr
    have := hnum.div hden (ne_of_gt (hI r hr))
    rw [one_mul] at this
    exact this
  refine monotoneOn_of_deriv_nonneg (convex_Ioo 0 r₀) ?_ ?_ ?_
  · intro r hr
    exact ((hN r hr).continuousAt).continuousWithinAt
  · rw [hint]
    intro r hr
    exact ((hN r hr).differentiableAt).differentiableWithinAt
  · rw [hint]
    intro r hr
    rw [(hN r hr).deriv]
    have hr0 : 0 < r := hr.1
    have hIpos := hI r hr
    have hnumeq : (E r + r * Ederiv r) * I r - (r * E r) * (I r / r + 2 * E r)
        = r * (Ederiv r * I r - 2 * E r ^ 2) := by
      field_simp
      ring
    rw [hnumeq]
    have h1 : 2 * E r ^ 2 ≤ 2 * (I r * F r) := by linarith [hCS r hr]
    have h2 : 2 * F r * I r ≤ Ederiv r * I r :=
      mul_le_mul_of_nonneg_right (hEF r hr) (le_of_lt hIpos)
    have h3 : 0 ≤ Ederiv r * I r - 2 * E r ^ 2 := by nlinarith
    positivity
