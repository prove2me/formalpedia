-- Prove2me | solution 1 for Kyprianou.Ch07.sumConvolutionTailIntegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:49:31.613196+00:00
-- url     : https://prove2.me/submissions/1df971e7-301d-4431-b2b2-2e6fdffc03f5

import Mathlib
import Definitions.Def_Kyprianou_Ch07_ConvolutionLargeJumpLaw
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem solution
    (mu nu : Measure Real) [SFinite nu] (x : Real) :
    (Kyprianou.Ch07.sumConvolution mu nu) (Set.Ioi x) =
      ∫⁻ a : Real, nu (Set.Ioi (x - a)) ∂mu := by
  let f : Real × Real → Real := fun z => z.1 + z.2
  have hf : Measurable f := measurable_fst.add measurable_snd
  have hs : MeasurableSet (f ⁻¹' Set.Ioi x) :=
    measurableSet_Ioi.preimage hf
  change (Measure.map f (mu.prod nu)) (Set.Ioi x) =
    ∫⁻ a : Real, nu (Set.Ioi (x - a)) ∂mu
  rw [Measure.map_apply hf measurableSet_Ioi]
  rw [Measure.prod_apply hs]
  congr 1
  funext a
  have hSet : (Prod.mk a) ⁻¹' (f ⁻¹' Set.Ioi x) =
      Set.Ioi (x - a) := by
    ext b
    simp only [Set.mem_preimage, Set.mem_Ioi, f]
    constructor <;> intro h <;> linarith
  rw [hSet]
