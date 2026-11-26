-- Prove2me | solution 1 for Kyprianou.Ch05.killedClockInfRestrictionV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:30:33.917003+00:00
-- url     : https://prove2.me/submissions/73d11d25-64f8-486c-a703-88f1ed6245b2

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_LeanLevy_RandomMeasure_PoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory Filter Set Complex Topology Kyprianou.Ch05
open scoped NNReal ENNReal Topology Classical
set_option autoImplicit false
theorem solution
    (S : Set ENNReal) (e : ENNReal) :
    sInf (S ∩ Iio e) = if sInf S < e then sInf S else ⊤ := by
  classical
  split_ifs with h
  · obtain ⟨z,hz,hze⟩ := sInf_lt_iff.mp h
    apply le_antisymm
    · apply le_sInf
      intro y hy
      by_cases hy' : y < e
      · exact sInf_le ⟨hy,hy'⟩
      · exact (sInf_le (show z ∈ S ∩ Iio e from ⟨hz,hze⟩)).trans
          (hze.le.trans (le_of_not_gt hy'))
    · exact sInf_le_sInf inter_subset_left
  · have he : S ∩ Iio e = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro y hy
      exact h ((sInf_le hy.1).trans_lt hy.2)
    rw [he,sInf_empty]
