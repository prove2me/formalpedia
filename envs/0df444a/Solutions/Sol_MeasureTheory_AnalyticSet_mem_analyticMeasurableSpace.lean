-- Prove2me | solution 1 for MeasureTheory.AnalyticSet.mem_analyticMeasurableSpace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:00:48.294709+00:00
-- url     : https://prove2.me/submissions/fd31c35b-efd6-4630-a946-6584ca6278ff

import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSet
import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSigmaAlgebra

set_option autoImplicit false
open MeasureTheory Set
noncomputable section
variable {X : Type*} [TopologicalSpace X]
open MeasureTheory MeasureTheory.AnalyticSet
namespace MeasureTheory.AnalyticSet
theorem _root_.solution {s : Set X}
    (hs : AnalyticSet s) :
    @MeasurableSet X (analyticMeasurableSpace X) s :=
  MeasurableSpace.measurableSet_generateFrom hs
end MeasureTheory.AnalyticSet
