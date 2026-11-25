-- Prove2me | solution 1 for GroundTheory.Automorphic.GJMatrix.measurePreserving_toEuclidPiConj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:09:35.412897+00:00
-- url     : https://prove2.me/submissions/53ae4125-ec78-4396-abcf-36da43a5528a

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceLatticePoisson
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJMatrixInfinite
import Theorems.Thm_GroundTheory_Automorphic_GJMatrix_measurePreserving_euclidPiEquiv
import Theorems.Thm_GroundTheory_Global_measurePreserving_mixedToEuclideanConj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open GroundTheory.Global NumberField NumberField.mixedEmbedding MeasureTheory Module Filter
open scoped FourierTransform SchwartzMap RealInnerProductSpace nonZeroDivisors Classical
set_option synthInstance.maxSize 1000
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable {ι : Type*} [Fintype ι]
namespace GroundTheory.Automorphic.GJMatrix
theorem _root_.solution :
    MeasurePreserving (toEuclidPiConj K (ι := ι)) (mixedMeasurePi K) volume :=
  (measurePreserving_euclidPiEquiv K).comp
    (measurePreserving_pi _ _ fun _ ↦ measurePreserving_mixedToEuclideanConj K)
end GroundTheory.Automorphic.GJMatrix
