-- Prove2me | solution 1 for Kyprianou.Ch05.monotoneMarkedCrossingClockUniqueV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:30:34.56931+00:00
-- url     : https://prove2.me/submissions/54fa0ee4-9f4e-42f0-a871-be227cd5ca1b

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
    (f : NNReal → ℝ) (hm : Monotone f) (x : ℝ) (t : NNReal)
    (ht : 0 < t) (hpost : x < f t) (hpre : Function.leftLim f t ≤ x) :
    sInf ((fun u : NNReal => (u : ENNReal)) '' {u : NNReal | 0 < u ∧ x < f u}) =
      (t : ENNReal) := by
  apply le_antisymm
  · exact sInf_le ⟨t,⟨ht,hpost⟩,rfl⟩
  · apply le_sInf
    rintro z ⟨u,hu,rfl⟩
    rw [ENNReal.coe_le_coe]
    by_contra! h
    exact (not_lt_of_ge ((hm.le_leftLim h).trans hpre)) hu.2
