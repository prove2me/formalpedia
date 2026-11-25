-- Prove2me | solution 1 for GroundTheory.Automorphic.Adele2.measurePreserving_toEuclid2Conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:50:43.885404+00:00
-- url     : https://prove2.me/submissions/a0003c52-b2e2-4090-b5e6-d8e70fd61b49

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceLatticePoisson
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_SummableNormIffAndTsumEqCoset2
import Theorems.Thm_GroundTheory_Global_measurePreserving_mixedToEuclideanConj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Adele2
open GroundTheory.Global NumberField NumberField.mixedEmbedding MeasureTheory Module Filter
open scoped FourierTransform SchwartzMap RealInnerProductSpace nonZeroDivisors Classical
set_option synthInstance.maxSize 1000
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
namespace GroundTheory.Automorphic.Adele2
theorem _root_.solution :
    MeasurePreserving (toEuclid2Conj K) (mixedMeasure2 K) volume := by
  have h1 := measurePreserving_finTwoArrow (selfDualMeasure K)
  have h2 := (measurePreserving_mixedToEuclideanConj K).prod
    (measurePreserving_mixedToEuclideanConj K)
  have h3 := WithLp.volume_preserving_toLp (euclidean.mixedSpace K) (euclidean.mixedSpace K)
  have h : ⇑(toEuclid2Conj K) = WithLp.toLp 2 ∘
      Prod.map (mixedToEuclideanConj K) (mixedToEuclideanConj K) ∘ MeasurableEquiv.finTwoArrow :=
    rfl
  rw [h]
  exact h3.comp (h2.comp h1)
end GroundTheory.Automorphic.Adele2
