-- Prove2me | solution 1 for Kyprianou.Ch05.predictableTimeCoordinateV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:46:19.476055+00:00
-- url     : https://prove2.me/submissions/ea0dbfeb-9f16-4404-ad35-f9c70ea2c10d

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
    {Omega : Type} [MeasurableSpace Omega] (F : Filtration NNReal inferInstance) :
    Measurable[F.predictable] (Prod.fst : NNReal × Omega → NNReal) := by
  apply measurable_of_Ioi
  intro t
  have he : (Prod.fst : NNReal × Omega → NNReal) ⁻¹' Ioi t =
      Ioi t ×ˢ (univ : Set Omega) := by
    ext z
    simp
  rw [he]
  exact measurableSet_predictable_Ioi_prod MeasurableSet.univ
