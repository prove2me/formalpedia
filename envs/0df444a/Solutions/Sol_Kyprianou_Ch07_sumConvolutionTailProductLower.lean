-- Prove2me | solution 1 for Kyprianou.Ch07.sumConvolutionTailProductLower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T23:46:18.379961+00:00
-- url     : https://prove2.me/submissions/93f0f7d4-966a-4f52-8c2e-20d1454d3c85

import Mathlib
import Definitions.Def_Kyprianou_Ch07_ConvolutionLargeJumpLaw
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem solution
    (G : Measure Real) [IsProbabilityMeasure G] (x T : Real) :
    G (Set.Ioi (x - T)) * G (Set.Ioi T) ≤
      (Kyprianou.Ch07.sumConvolution G G) (Set.Ioi x) := by
  let addPair : Real × Real → Real := fun z => z.1 + z.2
  have hMeas : Measurable addPair := measurable_fst.add measurable_snd
  have hSubset : (Set.Ioi (x - T) ×ˢ Set.Ioi T) ⊆
      addPair ⁻¹' Set.Ioi x := by
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    change x < a + b
    have ha' : x - T < a := ha
    have hb' : T < b := hb
    linarith
  change G (Set.Ioi (x - T)) * G (Set.Ioi T) ≤
    (Measure.map addPair (G.prod G)) (Set.Ioi x)
  rw [Measure.map_apply hMeas measurableSet_Ioi]
  calc
    _ = (G.prod G) (Set.Ioi (x - T) ×ˢ Set.Ioi T) := by
      rw [Measure.prod_prod]
    _ ≤ (G.prod G) (addPair ⁻¹' Set.Ioi x) := measure_mono hSubset
