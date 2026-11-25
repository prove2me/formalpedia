-- Prove2me | solution 1 for Kyprianou.Ch04.kw47_runningSup_contact_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T11:34:55.955469+00:00
-- url     : https://prove2.me/submissions/50059a76-6ace-4246-a7f3-0b61695d8e00

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_kw47_null_right_local_intervals
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_Ioc_eq_record_increment
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_no_real_atoms
import Theorems.Thm_AvramDividend_Classical_runningSup_right_local_const_of_positive_drawdown
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    {P : Measure Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (L : SpectrallyNegativeLevy P F) (w : Omega) :
    (dividendMeasure (runningSup L) w)
      {s : Real | 0 ≤ s ∧ L.X s.toNNReal w < runningSup L s.toNNReal w} = 0 := by 
  let mu := dividendMeasure (runningSup L) w
  letI : NullSingletonClass mu := ⟨runningSup_dividendMeasure_no_real_atoms L w⟩
  refine measure_mono_null (μ := mu) ?_
    (Kyprianou.Ch04.kw47_null_right_local_intervals mu)
  rintro s ⟨hs, hgap⟩
  have hp : 0 < reflectedSup L s.toNNReal w := by
    change 0 < runningSup L s.toNNReal w - L.X s.toNNReal w
    exact sub_pos.mpr hgap
  obtain ⟨v, hv, hflat⟩ := runningSup_right_local_const_of_positive_drawdown L w _ hp
  obtain ⟨r, hsr, hrv⟩ := exists_between hv
  refine ⟨(r : Real), ?_, ?_⟩
  · simpa [Real.coe_toNNReal _ hs] using (show (s.toNNReal : Real) < r by exact_mod_cast hsr)
  · change dividendMeasure (runningSup L) w (Ioc s (r : Real)) = 0
    rw [runningSup_dividendMeasure_Ioc_eq_record_increment,
      Real.toNNReal_coe, hflat r hsr.le hrv, sub_self, ENNReal.ofReal_zero]
