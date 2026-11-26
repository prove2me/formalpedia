-- Prove2me | solution 1 for Kyprianou.Ch04.expClockEarlyMassUpper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:38:06.938841+00:00
-- url     : https://prove2.me/submissions/c04f6185-3921-4f32-b60e-5bb91fa4d69c

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_expMeasure_strict_survival_real
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- The probability of an early exponential clock is bounded by its CDF. -/
theorem solution (q : ℝ) (hq : 0 < q) (T : NNReal) :
    ((expMeasure q).map Real.toNNReal (Iio T)).toReal ≤
      1 - Real.exp (-(q * (T : ℝ))) := by
  let Q := expMeasure q
  let : IsProbabilityMeasure Q := isProbabilityMeasure_expMeasure hq
  have hmap : Measurable Real.toNNReal := by fun_prop
  rw [Measure.map_apply hmap measurableSet_Iio]
  have hs : Real.toNNReal ⁻¹' Iio T ⊆ Iic (T : ℝ) := by
    intro r hr
    change r.toNNReal < T at hr
    exact (Real.le_coe_toNNReal r).trans (by exact_mod_cast hr.le)
  have hle := ENNReal.toReal_mono (measure_ne_top Q _) (measure_mono (μ := Q) hs)
  have htail := AvramDividend.Classical.avram_ws01e_b_expMeasure_strict_survival_real q (T : ℝ) hq T.coe_nonneg
  have hcomp : Q (Iic (T : ℝ)) = 1 - Q (Ioi (T : ℝ)) := by
    rw [← compl_Ioi, measure_compl measurableSet_Ioi (measure_ne_top Q _), measure_univ]
  have hleone : Q (Ioi (T : ℝ)) ≤ 1 := by
    simpa only [measure_univ] using (measure_mono (μ := Q) (subset_univ (Ioi (T : ℝ))))
  have he : (Q (Iic (T : ℝ))).toReal = 1 - Real.exp (-(q * (T : ℝ))) := by
    rw [hcomp, ENNReal.toReal_sub_of_le hleone ENNReal.one_ne_top]
    change (1 : ENNReal).toReal - (expMeasure q (Ioi (T : ℝ))).toReal = _
    rw [htail, ENNReal.toReal_one, ENNReal.toReal_ofReal (Real.exp_pos _).le]
  exact hle.trans_eq he
