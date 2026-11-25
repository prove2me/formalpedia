-- Prove2me | solution 1 for GroundTheory.Automorphic.Adele2.mixedFourier2_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:22:39.490904+00:00
-- url     : https://prove2.me/submissions/7ba4eb0d-e71b-476c-82ad-e0d25043f6df

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceLatticePoisson
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_SummableNormIffAndTsumEqCoset2
import Theorems.Thm_GroundTheory_Automorphic_Adele2_mixedPairing2_comm
import Theorems.Thm_GroundTheory_Automorphic_Adele2_mixedPairing2_neg_right

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
theorem _root_.solution (f : (Fin 2 → mixedSpace K) → ℂ) (x : Fin 2 → mixedSpace K) :
    mixedFourier2 K f (-x) = mixedFourierInv2 K f x := by
  rw [mixedFourier2, mixedFourierInv2]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  dsimp only
  rw [mixedPairing2_neg_right, neg_neg, mixedPairing2_comm]
end GroundTheory.Automorphic.Adele2
