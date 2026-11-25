-- Prove2me | solution 1 for GroundTheory.Automorphic.Adele2.mixedFourier2Schwartz_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:43:57.601812+00:00
-- url     : https://prove2.me/submissions/aadee640-959c-467d-8ef4-42595ee2680c

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceLatticePoisson
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_SummableNormIffAndTsumEqCoset2
import Theorems.Thm_GroundTheory_Automorphic_Adele2_mixedFourier2_eq

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
theorem _root_.solution (f : 𝓢(Fin 2 → mixedSpace K, ℂ)) :
    ⇑(mixedFourier2Schwartz K f) = mixedFourier2 K f := by
  funext y
  rw [mixedFourier2_eq]
  rfl
end GroundTheory.Automorphic.Adele2
