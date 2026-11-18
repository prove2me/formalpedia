-- Prove2me | solution 1 for Kyprianou.Ch07.finiteMeanUnitOscillationsSublinear
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T08:11:40.33387+00:00
-- url     : https://prove2.me/submissions/fa465d64-4fdd-4e07-9083-651e12f636cc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch07_UnitTimeOscillationObservables
import Definitions.Def_Kyprianou_Ch07_LevyMeanAndTailTests
import Theorems.Thm_Kyprianou_Ch07_unitOscillationTailSummable_of_finiteMean
import Theorems.Thm_Kyprianou_Ch07_unitOscillationSublinear_of_summableTails

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hX : Kyprianou.Ch06.IsRealLevyProcess P X)
    (hMoment : Integrable (fun omega => |X 1 omega|) P) :
    ∀ᵐ omega ∂P,
      Tendsto (fun n : Nat =>
        Kyprianou.Ch07.maximalUnitIncrement X n omega / (n : Real))
        atTop (nhds (0 : Real)) := by
  exact Kyprianou.Ch07.unitOscillationSublinear_of_summableTails P X
    (Kyprianou.Ch07.unitOscillationTailSummable_of_finiteMean
      P X hX hMoment)
