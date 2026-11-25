-- Prove2me | solution 1 for Kyprianou.Ch04.kw47_BV_exp_runningSup_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T20:06:23.466413+00:00
-- url     : https://prove2.me/submissions/0a8c21d3-0d57-44fa-9826-18e845713604

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_kw47_BV_runningSup_linear_ae_bound
import Theorems.Thm_AvramDividend_Classical_levy_runningSup_joint_time_path_measurable
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

/-- BV paths give deterministic compact-horizon exponential
integrability of their running maximum. -/
theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) (alpha : Real) (hAlpha : 0 ≤ alpha)
    (T : NNReal) :
    Integrable (fun w : Ω => Real.exp (alpha * runningSup L T w)) P := by
  letI : IsProbabilityMeasure P := L.isProbability
  have hU : Measurable (fun w : Ω => runningSup L T w) :=
    (levy_runningSup_joint_time_path_measurable L).comp
      (measurable_const.prodMk measurable_id)
  have hMeas : AEStronglyMeasurable
      (fun w : Ω => Real.exp (alpha * runningSup L T w)) P :=
    (measurable_const.mul hU).exp.aestronglyMeasurable
  have hBd : ∀ᵐ w ∂P,
      ‖Real.exp (alpha * runningSup L T w)‖ ≤
        Real.exp (alpha * max 0 ((T : Real) * L.drift)) := by
    filter_upwards [Kyprianou.Ch04.kw47_BV_runningSup_linear_ae_bound
      L hBV T] with w hw
    have he : Real.exp (alpha * runningSup L T w) ≤
        Real.exp (alpha * max 0 ((T : Real) * L.drift)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hw hAlpha)
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using he
  exact (integrable_const
    (Real.exp (alpha * max 0 ((T : Real) * L.drift)))).mono'
      hMeas hBd
