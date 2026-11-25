-- Prove2me | solution 1 for GroundTheory.Automorphic.GJMatrix.mixedFourierInvPi_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:22:58.038855+00:00
-- url     : https://prove2.me/submissions/19c3a2ad-b584-41e5-982a-4c958c0621e2

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceLatticePoisson
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJMatrixInfinite
import Theorems.Thm_GroundTheory_Automorphic_GJMatrix_mixedPairingPi_eq_inner
import Theorems.Thm_GroundTheory_Automorphic_GJMatrix_measurePreserving_toEuclidPiConj

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
    mixedFourierInvPi K f x = 𝓕⁻ (f ∘ (toEuclidPiConj K).symm) (toEuclidPi K x) := by
  rw [mixedFourierInvPi, Real.fourierInv_eq, ← (measurePreserving_toEuclidPiConj K).integral_comp
    (toEuclidPiConj K).toHomeomorph.measurableEmbedding]
  refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
  simp only [Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
  rw [mixedPairingPi_eq_inner, real_inner_comm]
end GroundTheory.Automorphic.GJMatrix
