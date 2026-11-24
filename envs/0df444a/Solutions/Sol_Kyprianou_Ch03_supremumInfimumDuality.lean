-- Prove2me | solution 1 for Kyprianou.Ch03.supremumInfimumDuality
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T07:10:05.603015+00:00
-- url     : https://prove2.me/submissions/05609821-f567-4c03-9415-448e973f8c56

import Mathlib
import Theorems.Thm_Kyprianou_Ch03_supInfDuality_dyadicPairLaw
import Theorems.Thm_Kyprianou_Ch03_supInfDuality_of_dyadicPairLaws
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LevyExtrema_SBA_runSup
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false


/-- Combine finite-grid reversal with the continuous-time limit. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal -> Omega -> Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (t : NNReal) (ht : 0 < t) :
    Measure.map
      (fun omega : Omega =>
        let supremum := LevyExtrema.SBA.runSup (fun s => X s omega) t
        (supremum, supremum - X t omega)) P =
    Measure.map
      (fun omega : Omega =>
        let infimum := sInf ((fun s : NNReal => X s omega) '' Set.Icc 0 t)
        (X t omega - infimum, -infimum)) P := by
  apply Kyprianou.Ch03.supInfDuality_of_dyadicPairLaws P X hX t ht
  intro n
  exact Kyprianou.Ch03.supInfDuality_dyadicPairLaw P X hX t ht n
