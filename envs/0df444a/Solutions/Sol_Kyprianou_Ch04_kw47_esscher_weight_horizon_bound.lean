-- Prove2me | solution 1 for Kyprianou.Ch04.kw47_esscher_weight_horizon_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T19:41:22.278016+00:00
-- url     : https://prove2.me/submissions/dcc9e958-89fd-4b2d-b02c-2563bef9784e

import Theorems.Thm_Kyprianou_Ch04_kw47_finite_horizon_predictable_weight_bound
import Theorems.Thm_AvramDividend_Classical_runningSup_isDividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_path_nonneg
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
open MeasureTheory AvramDividend.Classical
open scoped NNReal
set_option autoImplicit false
/-- Pathwise Esscher-product predictable weights have a deterministic finite-horizon envelope. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration NNReal (inferInstance : MeasurableSpace Ω)}
    (L : SpectrallyNegativeLevy P 𝓕)
    (alpha : Real) (hAlpha : 0 ≤ alpha) (T r : NNReal)
    (hrT : r ≤ T) (w : Ω) :
    Real.exp (-alpha * runningSup L r w + L.ψ alpha * (r : Real)) ≤
      Real.exp (|L.ψ alpha| * (T : Real)) := by
  have hU : 0 ≤ runningSup L r w :=
    dividendStrategy_path_nonneg (runningSup L) (runningSup_isDividendStrategy L) w r
  have hr : (0 : Real) ≤ (r : Real) := NNReal.coe_nonneg _
  have hrT' : (r : Real) ≤ (T : Real) := by exact_mod_cast hrT
  exact Kyprianou.Ch04.kw47_finite_horizon_predictable_weight_bound alpha (L.ψ alpha) (runningSup L r w)
    (r : Real) (T : Real) hAlpha hU hr hrT'
