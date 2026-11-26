-- Prove2me | solution 1 for MeasureTheory.Measure.map_fst_prod_of_isProbabilityMeasure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:11:26.047423+00:00
-- url     : https://prove2.me/submissions/48040cec-0668-4645-b11e-6c79a3581f4a

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
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure ν] :
    (μ.prod ν).map Prod.fst = μ := by
  rw [Measure.map_fst_prod, measure_univ, one_smul]
end MeasureTheory.Measure
