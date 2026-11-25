-- Prove2me | solution 1 for Kyprianou.Ch04.kw47_universal_exp_runningSup_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T20:14:21.303852+00:00
-- url     : https://prove2.me/submissions/e5c1e691-97a0-431e-b08d-66759a53be4c

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_kw47_BV_exp_runningSup_integrable
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_UBV_alltheta_finitehorizon_runningSup_exp_integrable
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Exponential running-supremum integrability holds for all
spectrally negative Lévy processes, independently of path variation. -/
theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F)
    (alpha : Real) (hAlpha : 0 ≤ alpha) (T : NNReal) :
    Integrable (fun w : Ω => Real.exp (alpha * runningSup L T w)) P := by
  by_cases hBV : L.BoundedVariation
  · exact Kyprianou.Ch04.kw47_BV_exp_runningSup_integrable
      L hBV alpha hAlpha T
  · exact avram_f6_original_UBV_alltheta_finitehorizon_runningSup_exp_integrable
      L hBV alpha hAlpha T
