-- Prove2me | solution 1 for GroundTheory.Automorphic.Adele2.mixedPairing2_neg_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:05:26.151853+00:00
-- url     : https://prove2.me/submissions/19b48f6d-ab05-4cc9-952b-bdcd2324a41f

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
theorem _root_.solution (x y : Fin 2 → mixedSpace K) :
    mixedPairing2 K x (-y) = -mixedPairing2 K x y := by
  simp only [mixedPairing2, Pi.neg_apply, map_neg, Finset.sum_neg_distrib]
end GroundTheory.Automorphic.Adele2
