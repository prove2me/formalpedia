-- Prove2me | solution 1 for GroundTheory.Automorphic.GJMatrix.mixedFourierPiSchwartz_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:37:32.820734+00:00
-- url     : https://prove2.me/submissions/82e26836-8ce7-4875-b222-35f24282d3e3

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceLatticePoisson
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJMatrixInfinite
import Theorems.Thm_GroundTheory_Automorphic_GJMatrix_mixedFourierPi_eq

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
theorem _root_.solution (f : 𝓢(ι → mixedSpace K, ℂ)) :
    ⇑(mixedFourierPiSchwartz K f) = mixedFourierPi K f := by
  funext y
  rw [mixedFourierPi_eq]
  rfl
end GroundTheory.Automorphic.GJMatrix
