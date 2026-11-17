-- Prove2me | solution 1 for Kyprianou.Ch07.exercise7_2StrongLawAllParts
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:13:04.730227+00:00
-- url     : https://prove2.me/submissions/159420e8-663f-4f51-a042-6396c9020858
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch07_finiteMeanMaximalUnitOscillationsIntegrable
import Theorems.Thm_Kyprianou_Ch07_finiteMeanUnitOscillationsSublinear
import Theorems.Thm_Kyprianou_Ch07_finiteMeanContinuousTimeLevyStrongLaw
import Theorems.Thm_Kyprianou_Ch07_positiveInfiniteMeanContinuousTimeLevyStrongLaw
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch07_UnitTimeOscillationObservables
import Definitions.Def_Kyprianou_Ch07_LevyMeanAndTailTests
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch07

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hX : Kyprianou.Ch06.IsRealLevyProcess P X) :
    ((Integrable (fun omega => |X 1 omega|) P →
      ((∀ n : Nat, Integrable (maximalUnitIncrement X n) P) ∧
       (∀ᵐ omega ∂P,
         Tendsto (fun n : Nat =>
           maximalUnitIncrement X n omega / (n : Real))
           atTop (nhds (0 : Real))) ∧
       (∀ᵐ omega ∂P,
         Tendsto (fun t : NNReal => X t omega / (t : Real))
           atTop (nhds (∫ omega, X 1 omega ∂P))))) ∧
     (positiveMeanPart P X = ⊤ ∧ negativeMeanPart P X < ⊤ →
       (∀ᵐ omega ∂P,
         Tendsto (fun t : NNReal => X t omega / (t : Real))
           atTop atTop))) := by
  constructor
  · intro hMoment
    exact ⟨
      Kyprianou.Ch07.finiteMeanMaximalUnitOscillationsIntegrable P X hX hMoment,
      Kyprianou.Ch07.finiteMeanUnitOscillationsSublinear P X hX hMoment,
      Kyprianou.Ch07.finiteMeanContinuousTimeLevyStrongLaw P X hX hMoment⟩
  · intro hMean
    exact Kyprianou.Ch07.positiveInfiniteMeanContinuousTimeLevyStrongLaw P X hX hMean
