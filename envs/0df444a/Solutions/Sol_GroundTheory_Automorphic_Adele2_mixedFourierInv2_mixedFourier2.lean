-- Prove2me | solution 1 for GroundTheory.Automorphic.Adele2.mixedFourierInv2_mixedFourier2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:54:10.233797+00:00
-- url     : https://prove2.me/submissions/a7f55052-e8fb-40ac-bae8-f7a55c90332e

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceLatticePoisson
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_SummableNormIffAndTsumEqCoset2
import Theorems.Thm_GroundTheory_Automorphic_Adele2_mixedFourier2_eq
import Theorems.Thm_GroundTheory_Automorphic_Adele2_mixedFourierInv2_eq

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
    (x : Fin 2 → mixedSpace K) : mixedFourierInv2 K (mixedFourier2 K f) x = f x := by
  set F : 𝓢(WithLp 2 (euclidean.mixedSpace K × euclidean.mixedSpace K), ℂ) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (toEuclid2 K).symm f with hFdef
  have hF : (F : WithLp 2 (euclidean.mixedSpace K × euclidean.mixedSpace K) → ℂ) =
      f ∘ (toEuclid2 K).symm := rfl
  have h1 : mixedFourier2 K f ∘ (toEuclid2Conj K).symm =
      𝓕 (F : WithLp 2 (euclidean.mixedSpace K × euclidean.mixedSpace K) → ℂ) := by
    funext v
    rw [Function.comp_apply, mixedFourier2_eq, ContinuousLinearEquiv.apply_symm_apply, hF]
  have h2 : Integrable
      (𝓕 (F : WithLp 2 (euclidean.mixedSpace K × euclidean.mixedSpace K) → ℂ)) := by
    rw [← SchwartzMap.fourier_coe]
    exact (𝓕 F).integrable
  rw [mixedFourierInv2_eq, h1, F.continuous.fourierInv_fourier_eq F.integrable h2, hF,
    Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
end GroundTheory.Automorphic.Adele2
