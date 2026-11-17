-- Prove2me | solution 1 for Kyprianou.Ch07.negativeDriftReflectedIffPositiveDrift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:55:01.046308+00:00
-- url     : https://prove2.me/submissions/53398bd2-1723-4688-b488-f0efbc982cca

import Mathlib
import Definitions.Def_Kyprianou_Ch07_DriftOscillationObservables
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (X : NNReal → Omega → Real) :
    Kyprianou.Ch07.DriftsToNegInfinity P (fun t omega => -X t omega) ↔
      Kyprianou.Ch07.DriftsToPosInfinity P X := by
  constructor
  · intro h
    change (∀ᵐ omega ∂P,
      Tendsto (fun t : NNReal => -X t omega) atTop atBot) at h
    change (∀ᵐ omega ∂P,
      Tendsto (fun t : NNReal => X t omega) atTop atTop)
    filter_upwards [h] with omega hlim
    have hn := Filter.tendsto_neg_atBot_atTop.comp hlim
    simpa only [Function.comp_def, neg_neg] using hn
  · intro h
    change (∀ᵐ omega ∂P,
      Tendsto (fun t : NNReal => X t omega) atTop atTop) at h
    change (∀ᵐ omega ∂P,
      Tendsto (fun t : NNReal => -X t omega) atTop atBot)
    filter_upwards [h] with omega hlim
    exact Filter.tendsto_neg_atTop_atBot.comp hlim
