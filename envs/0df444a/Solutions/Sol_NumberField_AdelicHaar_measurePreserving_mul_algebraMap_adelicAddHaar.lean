-- Prove2me | solution 1 for NumberField.AdelicHaar.measurePreserving_mul_algebraMap_adelicAddHaar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/883898ac-90db-5e97-baa6-6efa6c1ddc4a

import Definitions.Def_NumberField_AdelicBox
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Theorems.Thm_NumberField_AdeleRing_measurePreserving_mul_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicHaar_measurePreserving_mul_algebraMap_adelicAddHaar

set_option autoImplicit false

open NumberField MeasureTheory MeasureTheory.Measure

attribute [local instance] NumberField.AdelicHaar.adeleBorel

theorem FltWs24.regular_adelicAddHaar (F : Type) [Field F] [NumberField F] :
    (AdelicHaar.adelicAddHaar (𝓞 F) F).Regular := by
  haveI := AdelicHaar.borelSpace_adeleBorel (𝓞 F) F
  first
    | exact (inferInstance : (Measure.addHaar : Measure (AdeleRing (𝓞 F) F)).Regular)
    | (unfold AdelicHaar.adelicAddHaar Measure.addHaar; infer_instance)
    | (delta NumberField.AdelicHaar.adelicAddHaar; unfold Measure.addHaar; infer_instance)

theorem solution
    (F : Type) [Field F] [NumberField F] (a : F) (ha : a ≠ 0) :
    MeasureTheory.MeasurePreserving (fun x => algebraMap F (AdeleRing (𝓞 F) F) a * x)
      (AdelicHaar.adelicAddHaar (𝓞 F) F) (AdelicHaar.adelicAddHaar (𝓞 F) F) := by
  haveI := AdelicHaar.borelSpace_adeleBorel (𝓞 F) F
  haveI := AdelicHaar.isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  haveI := FltWs24.regular_adelicAddHaar F
  exact NumberField.AdeleRing.measurePreserving_mul_algebraMap F _ a ha

end S_NumberField_AdelicHaar_measurePreserving_mul_algebraMap_adelicAddHaar
end P2MW
export P2MW.S_NumberField_AdelicHaar_measurePreserving_mul_algebraMap_adelicAddHaar (solution)
