-- Prove2me | solution 1 for Kyprianou.Ch07.sumConvolutionComm
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T23:26:57.196208+00:00
-- url     : https://prove2.me/submissions/812b4a26-42d8-4c94-8fcd-9e18d10938e0

import Mathlib
import Definitions.Def_Kyprianou_Ch07_ConvolutionLargeJumpLaw
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem solution
    (mu nu : Measure Real) [SFinite mu] [SFinite nu] :
    Kyprianou.Ch07.sumConvolution mu nu =
      Kyprianou.Ch07.sumConvolution nu mu := by
  let addPair : Real × Real → Real := fun z => z.1 + z.2
  have hadd : Measurable addPair := measurable_fst.add measurable_snd
  have hswap : Measurable (Prod.swap : Real × Real → Real × Real) :=
    measurable_snd.prodMk measurable_fst
  have hprod : Measure.map Prod.swap (nu.prod mu) = mu.prod nu :=
    Measure.prod_swap
  change Measure.map addPair (mu.prod nu) =
    Measure.map addPair (nu.prod mu)
  calc
    Measure.map addPair (mu.prod nu) =
      Measure.map addPair (Measure.map Prod.swap (nu.prod mu)) := by
        rw [hprod]
    _ = Measure.map (addPair ∘ Prod.swap) (nu.prod mu) := by
        rw [Measure.map_map hadd hswap]
    _ = Measure.map addPair (nu.prod mu) := by
        have hfun : addPair ∘ Prod.swap = addPair := by
          funext z
          simp [addPair, Function.comp_def, add_comm]
        rw [hfun]
