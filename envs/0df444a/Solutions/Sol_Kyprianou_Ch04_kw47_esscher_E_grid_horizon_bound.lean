-- Prove2me | solution 1 for Kyprianou.Ch04.kw47_esscher_E_grid_horizon_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T20:07:07.07185+00:00
-- url     : https://prove2.me/submissions/9a85faa9-1fae-4b7c-9200-dc79fb11539e

import Mathlib
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A finite-horizon Esscher exponential is dominated pathwise by
the exponential of the running maximum plus a time-only factor. -/
theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F)
    (alpha : Real) (hAlpha : 0 ≤ alpha)
    (T r : NNReal) (hrT : r ≤ T) (w : Ω) :
    |Real.exp (alpha * L.X r w - L.ψ alpha * (r : Real))| ≤
      Real.exp (alpha * runningSup L T w +
        |L.ψ alpha| * (T : Real)) := by
  have hUX := (runningSup_monotone_and_path_le L w).2 r
  have hUT := (runningSup_monotone_and_path_le L w).1 hrT
  have hXUpper : L.X r w ≤ runningSup L T w :=
    hUX.trans hUT
  have h1 : alpha * L.X r w ≤ alpha * runningSup L T w :=
    mul_le_mul_of_nonneg_left hXUpper hAlpha
  have hr0 : 0 ≤ (r : Real) := NNReal.coe_nonneg _
  have hrTR : (r : Real) ≤ (T : Real) := by exact_mod_cast hrT
  have h2 : -L.ψ alpha * (r : Real) ≤ |L.ψ alpha| * (r : Real) :=
    mul_le_mul_of_nonneg_right (neg_le_abs _) hr0
  have h3 : |L.ψ alpha| * (r : Real) ≤
      |L.ψ alpha| * (T : Real) :=
    mul_le_mul_of_nonneg_left hrTR (abs_nonneg _)
  have hArg : alpha * L.X r w - L.ψ alpha * (r : Real) ≤
      alpha * runningSup L T w + |L.ψ alpha| * (T : Real) := by
    nlinarith
  have he := Real.exp_le_exp.mpr hArg
  simpa only [abs_of_pos (Real.exp_pos _)] using he
