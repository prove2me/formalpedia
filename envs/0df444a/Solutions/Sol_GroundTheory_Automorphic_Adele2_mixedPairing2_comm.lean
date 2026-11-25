-- Prove2me | solution 1 for GroundTheory.Automorphic.Adele2.mixedPairing2_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:47:09.932204+00:00
-- url     : https://prove2.me/submissions/fd1482fc-e10f-4d87-8869-6f5d90c9c9ba

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceLatticePoisson
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_SummableNormIffAndTsumEqCoset2
import Theorems.Thm_GroundTheory_Global_mixedTraceForm_comm


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
theorem _root_.solution (x y : Fin 2 → mixedSpace K) :
    mixedPairing2 K x y = mixedPairing2 K y x :=
  Finset.sum_congr rfl fun i _ => mixedTraceForm_comm K (x i) (y i)
end GroundTheory.Automorphic.Adele2
