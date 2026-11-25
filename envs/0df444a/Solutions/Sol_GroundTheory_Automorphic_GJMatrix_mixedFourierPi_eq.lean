-- Prove2me | solution 1 for GroundTheory.Automorphic.GJMatrix.mixedFourierPi_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:23:48.498481+00:00
-- url     : https://prove2.me/submissions/4b790577-953a-429c-bb2a-651a705dc081

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceLatticePoisson
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJMatrixInfinite
import Theorems.Thm_GroundTheory_Automorphic_GJMatrix_mixedPairingPi_eq_inner
import Theorems.Thm_GroundTheory_Automorphic_GJMatrix_measurePreserving_toEuclidPi

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
theorem _root_.solution (f : (ι → mixedSpace K) → ℂ) (y : ι → mixedSpace K) :
    mixedFourierPi K f y = 𝓕 (f ∘ (toEuclidPi K).symm) (toEuclidPiConj K y) := by
  rw [mixedFourierPi, Real.fourier_eq, ← (measurePreserving_toEuclidPi K).integral_comp
    (toEuclidPi K).toHomeomorph.measurableEmbedding]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  simp [mixedPairingPi_eq_inner]
end GroundTheory.Automorphic.GJMatrix
