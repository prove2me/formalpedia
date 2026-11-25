-- Prove2me | solution 1 for GroundTheory.Automorphic.Adele2.measurePreserving_toEuclid2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:47:15.690868+00:00
-- url     : https://prove2.me/submissions/70e013d6-cf26-4803-9327-631f63d45daa

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceLatticePoisson
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_SummableNormIffAndTsumEqCoset2
import Theorems.Thm_GroundTheory_Global_measurePreserving_mixedToEuclidean


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
    MeasurePreserving (toEuclid2 K) (mixedMeasure2 K) volume := by
  have h1 := measurePreserving_finTwoArrow (selfDualMeasure K)
  have h2 := (measurePreserving_mixedToEuclidean K).prod (measurePreserving_mixedToEuclidean K)
  have h3 := WithLp.volume_preserving_toLp (euclidean.mixedSpace K) (euclidean.mixedSpace K)
  have h : ⇑(toEuclid2 K) = WithLp.toLp 2 ∘
      Prod.map (mixedToEuclidean K) (mixedToEuclidean K) ∘ MeasurableEquiv.finTwoArrow := rfl
  rw [h]
  exact h3.comp (h2.comp h1)
end GroundTheory.Automorphic.Adele2
