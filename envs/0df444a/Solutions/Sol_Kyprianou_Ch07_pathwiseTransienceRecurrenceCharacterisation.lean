-- Prove2me | solution 1 for Kyprianou.Ch07.pathwiseTransienceRecurrenceCharacterisation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:22:31.291313+00:00
-- url     : https://prove2.me/submissions/4d2f3f08-533f-40dc-9c5c-15f726b94bec
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch07_pathwiseTransienceIffEscapesCompacts
import Theorems.Thm_Kyprianou_Ch07_pathwiseRecurrenceIffReturnsEveryPoint
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch07_TransienceAndRecurrence
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
    ((IsTransientLevyProcess P X ↔
      ∀ᵐ omega ∂P,
        Tendsto (fun t : NNReal => |X t omega|) atTop atTop) ∧
     (¬ Kyprianou.Ch06.IsCompoundPoissonProcess P X →
      (IsRecurrentLevyProcess P X ↔
        ∀ x : Real, ∀ᵐ omega ∂P,
          ∀ epsilon : Real, 0 < epsilon →
            ∀ T : NNReal, ∃ t : NNReal,
              T ≤ t ∧ |X t omega - x| < epsilon))) := by
  constructor
  · exact Kyprianou.Ch07.pathwiseTransienceIffEscapesCompacts P X hX
  · intro hNonCompound
    exact Kyprianou.Ch07.pathwiseRecurrenceIffReturnsEveryPoint
      P X hX hNonCompound
