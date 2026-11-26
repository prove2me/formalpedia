-- Prove2me | solution 1 for MeasureTheory.Measure.map_snd_prod_of_isProbabilityMeasure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:11:02.132012+00:00
-- url     : https://prove2.me/submissions/367c4b31-b6e7-4fce-b60f-b2aae95d6285

import Definitions.Def_BicausalOT_MultiPeriod
import Definitions.Def_BicausalOT_ValueRepresentation
import Mathlib.MeasureTheory.Measure.Prod
import Definitions.Def_BicausalOT_FeasNonempty
import Theorems.Thm_MultiPeriod_Feas_measure_univ


set_option autoImplicit false
open MeasureTheory Set ENNReal
noncomputable section
namespace MeasureTheory.Measure
theorem _root_.solution
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [SFinite ν] :
    (μ.prod ν).map Prod.snd = ν := by
  rw [Measure.map_snd_prod, measure_univ, one_smul]
end MeasureTheory.Measure
