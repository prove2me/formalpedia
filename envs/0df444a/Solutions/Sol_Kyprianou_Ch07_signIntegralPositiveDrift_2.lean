-- Prove2me | solution 2 for Kyprianou.Ch07.signIntegralPositiveDrift
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:54:27.783092+00:00
-- url     : https://prove2.me/submissions/58c93b9c-7f19-4888-bb79-1f9256e24ab8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch07_DriftOscillationObservables
import Theorems.Thm_Kyprianou_Ch07_realLevyProcessNegation
import Theorems.Thm_Kyprianou_Ch07_signIntegralReflect
import Theorems.Thm_Kyprianou_Ch07_signIntegralNegativeDrift
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
    (hX : Kyprianou.Ch06.IsRealLevyProcess P X)
    (hFinite : Kyprianou.Ch07.nonpositiveSignIntegral P X < ⊤) :
    Kyprianou.Ch07.DriftsToPosInfinity P X := by
  have hXneg : Kyprianou.Ch06.IsRealLevyProcess P
      (fun t omega => -X t omega) :=
    Kyprianou.Ch07.realLevyProcessNegation P X hX
  have hFiniteNeg :
      Kyprianou.Ch07.nonnegativeSignIntegral P
        (fun t omega => -X t omega) < ⊤ := by
    rw [Kyprianou.Ch07.signIntegralReflect]
    exact hFinite
  have hNeg := Kyprianou.Ch07.signIntegralNegativeDrift
    P (fun t omega => -X t omega) hXneg hFiniteNeg
  change (∀ᵐ omega ∂P,
    Tendsto (fun t : NNReal => -X t omega) atTop atBot) at hNeg
  change (∀ᵐ omega ∂P,
    Tendsto (fun t : NNReal => X t omega) atTop atTop)
  filter_upwards [hNeg] with omega hlim
  have hn := Filter.tendsto_neg_atBot_atTop.comp hlim
  simpa only [Function.comp_def, neg_neg] using hn
