-- Prove2me | solution 1 for Kyprianou.Ch07.convolutionPowerOne
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:35:06.001079+00:00
-- url     : https://prove2.me/submissions/ff8df8c7-8c48-4516-b5eb-16a7b1271817

import Mathlib
import Definitions.Def_Kyprianou_Ch07_ConvolutionLargeJumpLaw
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem solution
    (G : Measure Real) [IsProbabilityMeasure G] :
    Kyprianou.Ch07.convolutionPower G 1 = G := by
  change Measure.map (fun z : Real × Real => z.1 + z.2)
    ((Measure.dirac (0 : Real)).prod G) = G
  rw [Measure.dirac_prod (0 : Real)]
  have hm : Measurable (fun y : Real => ((0 : Real), y)) :=
    measurable_const.prodMk measurable_id
  change Measure.map (fun z : Real × Real => z.1 + z.2)
    (Measure.map (fun y : Real => ((0 : Real), y)) G) = G
  have hAdd : Measurable (fun z : Real × Real => z.1 + z.2) :=
    measurable_fst.add measurable_snd
  rw [Measure.map_map hAdd hm]
  have hfunc : ((fun z : Real × Real => z.1 + z.2) ∘
      (fun y : Real => ((0 : Real), y))) = id := by
    funext y
    simp [Function.comp_def]
  rw [hfunc]
  exact Measure.map_id
