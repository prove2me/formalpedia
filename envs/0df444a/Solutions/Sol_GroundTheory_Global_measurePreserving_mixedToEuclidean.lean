-- Prove2me | solution 1 for GroundTheory.Global.measurePreserving_mixedToEuclidean
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:26:40.611692+00:00
-- url     : https://prove2.me/submissions/c10fe5ca-8e77-40c1-a8c9-3a8ad2661b7b

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TracePairing
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceFourier
import Theorems.Thm_GroundTheory_Global_measurePreserving_mapComplexCoord
import Theorems.Thm_GroundTheory_Global_det_sqrtTwoSMulComplex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module MeasureTheory
open scoped Classical ComplexConjugate RealInnerProductSpace FourierTransform Real ENNReal SchwartzMap
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution :
    MeasurePreserving (mixedToEuclidean K) (selfDualMeasure K) volume :=
  (euclidean.volumePreserving_toMixed_symm K).comp
    (measurePreserving_mapComplexCoord K _ (by rw [det_sqrtTwoSMulComplex]; norm_num))
end GroundTheory.Global
