-- Prove2me | solution 1 for GroundTheory.Automorphic.Adele2.mixedFourierInv2_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:29:37.653487+00:00
-- url     : https://prove2.me/submissions/7a397001-44b2-4e5e-b8dc-57cc8b6a98e6

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceLatticePoisson
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_SummableNormIffAndTsumEqCoset2
import Theorems.Thm_GroundTheory_Automorphic_Adele2_mixedPairing2_eq_inner
import Theorems.Thm_GroundTheory_Automorphic_Adele2_measurePreserving_toEuclid2Conj

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
theorem _root_.solution (f : (Fin 2 → mixedSpace K) → ℂ) (x : Fin 2 → mixedSpace K) :
    mixedFourierInv2 K f x = 𝓕⁻ (f ∘ (toEuclid2Conj K).symm) (toEuclid2 K x) := by
  rw [mixedFourierInv2, Real.fourierInv_eq, ← (measurePreserving_toEuclid2Conj K).integral_comp
    (toEuclid2Conj K).toHomeomorph.measurableEmbedding]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
  rw [mixedPairing2_eq_inner, real_inner_comm]
end GroundTheory.Automorphic.Adele2
