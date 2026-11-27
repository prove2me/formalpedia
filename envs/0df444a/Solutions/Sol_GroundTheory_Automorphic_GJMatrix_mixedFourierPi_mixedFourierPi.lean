-- Prove2me | solution 1 for GroundTheory.Automorphic.GJMatrix.mixedFourierPi_mixedFourierPi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:43:02.359881+00:00
-- url     : https://prove2.me/submissions/bbccb271-98d9-4588-8458-a2212b2940ef

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceLatticePoisson
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJMatrixInfinite
import Theorems.Thm_GroundTheory_Automorphic_GJMatrix_mixedFourierInvPi_mixedFourierPi
import Theorems.Thm_GroundTheory_Automorphic_GJMatrix_mixedFourierPi_neg

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
theorem _root_.solution (f : 𝓢(ι → mixedSpace K, ℂ))
    (x : ι → mixedSpace K) : mixedFourierPi K (mixedFourierPi K f) x = f (-x) := by
  rw [← neg_neg x, mixedFourierPi_neg, mixedFourierInvPi_mixedFourierPi, neg_neg]
end GroundTheory.Automorphic.GJMatrix
