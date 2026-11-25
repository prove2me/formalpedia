-- Prove2me | solution 1 for GroundTheory.Automorphic.GJMatrix.mixedFourierPi_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:22:25.128152+00:00
-- url     : https://prove2.me/submissions/55bb51ae-d647-4259-9135-b16510432253

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceLatticePoisson
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJMatrixInfinite
import Theorems.Thm_GroundTheory_Automorphic_GJMatrix_mixedPairingPi_comm
import Theorems.Thm_GroundTheory_Automorphic_GJMatrix_mixedPairingPi_neg_right

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
theorem _root_.solution (f : (ι → mixedSpace K) → ℂ) (x : ι → mixedSpace K) :
    mixedFourierPi K f (-x) = mixedFourierInvPi K f x := by
  rw [mixedFourierPi, mixedFourierInvPi]
  refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
  dsimp only
  rw [mixedPairingPi_neg_right, neg_neg, mixedPairingPi_comm]
end GroundTheory.Automorphic.GJMatrix
