-- Prove2me | solution 1 for GroundTheory.Global.mixedFourierInv_mixedFourier
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:46:25.642873+00:00
-- url     : https://prove2.me/submissions/75ab7d1f-c242-4824-b954-d25f26827a16

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TracePairing
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceFourier
import Theorems.Thm_GroundTheory_Global_mixedFourier_eq
import Theorems.Thm_GroundTheory_Global_mixedFourierInv_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module MeasureTheory
open scoped Classical ComplexConjugate RealInnerProductSpace FourierTransform Real ENNReal SchwartzMap
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [CompleteSpace E]
namespace GroundTheory.Global
theorem _root_.solution (f : 𝓢(mixedSpace K, E)) (x : mixedSpace K) :
    mixedFourierInv K (mixedFourier K f) x = f x := by
  set F : 𝓢(euclidean.mixedSpace K, E) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (mixedToEuclidean K).symm f with hFdef
  have hF : (F : euclidean.mixedSpace K → E) = f ∘ (mixedToEuclidean K).symm := rfl
  have h1 : mixedFourier K f ∘ (mixedToEuclideanConj K).symm = 𝓕 (F : euclidean.mixedSpace K → E) := by
    funext v
    rw [Function.comp_apply, mixedFourier_eq, ContinuousLinearEquiv.apply_symm_apply, hF]
  have h2 : Integrable (𝓕 (F : euclidean.mixedSpace K → E)) := by
    rw [← SchwartzMap.fourier_coe]
    exact (𝓕 F).integrable
  rw [mixedFourierInv_eq, h1, F.continuous.fourierInv_fourier_eq F.integrable h2, hF,
    Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
end GroundTheory.Global
