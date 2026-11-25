-- Prove2me | solution 1 for GroundTheory.Automorphic.Adele2.measurePreserving_toEuclid2_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:05:25.410397+00:00
-- url     : https://prove2.me/submissions/02191626-39b0-40f3-a39b-bc0e6b3d904b

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceLatticePoisson
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_SummableNormIffAndTsumEqCoset2
import Theorems.Thm_GroundTheory_Automorphic_Adele2_measurePreserving_toEuclid2

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
    MeasurePreserving (toEuclid2 K).symm volume (mixedMeasure2 K) := by
  have : MeasurePreserving (toEuclid2 K).toHomeomorph.toMeasurableEquiv
      (mixedMeasure2 K) volume := measurePreserving_toEuclid2 K
  exact this.symm
end GroundTheory.Automorphic.Adele2
