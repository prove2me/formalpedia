-- Prove2me | solution 1 for GroundTheory.Automorphic.Adele2.toEuclid2Conj_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:06:10.871506+00:00
-- url     : https://prove2.me/submissions/17f2f010-df09-4cce-9c2c-3856b1885507

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceLatticePoisson
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_SummableNormIffAndTsumEqCoset2

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
theorem _root_.solution (x : Fin 2 → mixedSpace K) :
    toEuclid2Conj K x =
      WithLp.toLp 2 (mixedToEuclideanConj K (x 0), mixedToEuclideanConj K (x 1)) := rfl
end GroundTheory.Automorphic.Adele2
