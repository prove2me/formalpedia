-- Prove2me | solution 1 for GroundTheory.Automorphic.Adele2.mixedFourier2_mixedFourier2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:45:22.100355+00:00
-- url     : https://prove2.me/submissions/e4af6927-cc3f-4553-b1f3-e13048efbfa3

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceLatticePoisson
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_SummableNormIffAndTsumEqCoset2
import Theorems.Thm_GroundTheory_Automorphic_Adele2_mixedFourierInv2_mixedFourier2
import Theorems.Thm_GroundTheory_Automorphic_Adele2_mixedFourier2_neg

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
theorem _root_.solution (f : 𝓢(Fin 2 → mixedSpace K, ℂ))
    (x : Fin 2 → mixedSpace K) : mixedFourier2 K (mixedFourier2 K f) x = f (-x) := by
  rw [← neg_neg x, mixedFourier2_neg, mixedFourierInv2_mixedFourier2, neg_neg]
end GroundTheory.Automorphic.Adele2
