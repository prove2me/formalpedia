-- Prove2me | solution 1 for GroundTheory.Automorphic.GJMatrix.mixedFourierInvPi_mixedFourierPi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:37:31.194058+00:00
-- url     : https://prove2.me/submissions/8001c9b6-9e5c-4c32-b093-b2556b0e030c

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceLatticePoisson
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJMatrixInfinite
import Theorems.Thm_GroundTheory_Automorphic_GJMatrix_mixedFourierPi_eq
import Theorems.Thm_GroundTheory_Automorphic_GJMatrix_mixedFourierInvPi_eq

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
    (x : ι → mixedSpace K) : mixedFourierInvPi K (mixedFourierPi K f) x = f x := by
  set F : 𝓢(EuclidPi K ι, ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (toEuclidPi K).symm f
    with hFdef
  have hF : (F : EuclidPi K ι → ℂ) = f ∘ (toEuclidPi K).symm := rfl
  have h1 : mixedFourierPi K f ∘ (toEuclidPiConj K).symm = 𝓕 (F : EuclidPi K ι → ℂ) := by
    funext v
    rw [Function.comp_apply, mixedFourierPi_eq, ContinuousLinearEquiv.apply_symm_apply, hF]
  have h2 : Integrable (𝓕 (F : EuclidPi K ι → ℂ)) := by
    rw [← SchwartzMap.fourier_coe]
    exact (𝓕 F).integrable
  rw [mixedFourierInvPi_eq, h1, F.continuous.fourierInv_fourier_eq F.integrable h2, hF,
    Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
end GroundTheory.Automorphic.GJMatrix
