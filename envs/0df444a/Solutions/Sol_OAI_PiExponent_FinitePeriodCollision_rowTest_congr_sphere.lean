-- Prove2me | solution 1 for OAI.PiExponent.FinitePeriodCollision.rowTest_congr_sphere
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T18:32:13.643586+00:00
-- url     : https://prove2.me/submissions/97c7fed6-91b4-49d9-9a76-676b165d9590

import Definitions.Def_OAI_PiExponent_FinitePeriodAnalytic
open scoped BigOperators
open OAI.PiExponent
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation
open OAI.PiExponent.FinitePeriodCollision

/-- The Cauchy row test `rowTest ell f` is the normalized Taylor coefficient of `f` at the centre
`0`, measured on the circle of radius `1/2`; hence it only depends on the values of `f` on that
circle. -/
theorem solution {f g : ℂ → ℂ} (ell : ℕ)
    (hfg : ∀ z ∈ Metric.sphere (0 : ℂ) (1 / 2), f z = g z) :
    rowTest ell f = rowTest ell g := by
  simp only [rowTest, cauchyPowerSeries_apply]
  congr 1
  apply circleIntegral.integral_congr (by norm_num)
  intro z hz
  change (1 / (z - 0)) ^ ell • (z - 0)⁻¹ • f z =
    (1 / (z - 0)) ^ ell • (z - 0)⁻¹ • g z
  rw [hfg z hz]
