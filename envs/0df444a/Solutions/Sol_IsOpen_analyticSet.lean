-- Prove2me | solution 1 for IsOpen.analyticSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:00:48.964414+00:00
-- url     : https://prove2.me/submissions/9ac4de9f-17b9-4997-ac7f-c394df397b30

import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSet
import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSigmaAlgebra

set_option autoImplicit false
open MeasureTheory Set
noncomputable section
variable {X : Type*} [TopologicalSpace X]
namespace IsOpen
theorem _root_.solution [PolishSpace X] {s : Set X} (hs : IsOpen s) :
    AnalyticSet s := by
  rw [show s = id '' s from (image_id s).symm]
  exact hs.analyticSet_image continuous_id
end IsOpen
