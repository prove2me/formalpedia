-- Prove2me | solution 1 for MeasureTheory.AnalyticSet.compl_mem_analyticMeasurableSpace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:03:20.849862+00:00
-- url     : https://prove2.me/submissions/3d89bb7f-97d0-4b06-9130-6c5215db7a8d

import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSet
import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSigmaAlgebra
import Theorems.Thm_MeasureTheory_AnalyticSet_mem_analyticMeasurableSpace

set_option autoImplicit false
open MeasureTheory Set
noncomputable section
variable {X : Type*} [TopologicalSpace X]
open MeasureTheory MeasureTheory.AnalyticSet
namespace MeasureTheory.AnalyticSet
theorem _root_.solution {s : Set X}
    (hs : AnalyticSet s) :
    @MeasurableSet X (analyticMeasurableSpace X) sᶜ :=
  hs.mem_analyticMeasurableSpace.compl
end MeasureTheory.AnalyticSet
