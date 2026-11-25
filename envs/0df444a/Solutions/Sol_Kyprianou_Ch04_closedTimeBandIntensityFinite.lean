-- Prove2me | solution 1 for Kyprianou.Ch04.closedTimeBandIntensityFinite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T23:56:10.634797+00:00
-- url     : https://prove2.me/submissions/8afaa3ba-665c-4b71-b616-06dccd683bc4

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch04
theorem solution
    (levyMeasure : Measure Real) [SigmaFinite levyMeasure]
    (t : NNReal) (B : Set Real) (hB : levyMeasure B < ⊤) :
    referenceIntensity levyMeasure (Set.Icc (0 : Real) (t : Real) ×ˢ B) ≠ ⊤ := by
  have h : Set.Icc (0 : Real) (t : Real) ∩ Set.Ici 0 =
      Set.Icc (0 : Real) (t : Real) := Set.inter_eq_left.mpr (fun _ hx => hx.1)
  rw [referenceIntensity, Measure.prod_prod, Measure.restrict_apply measurableSet_Icc,
    h, Real.volume_Icc]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hB.ne
