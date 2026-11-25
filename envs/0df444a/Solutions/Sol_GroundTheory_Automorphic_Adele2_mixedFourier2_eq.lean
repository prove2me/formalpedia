-- Prove2me | solution 1 for GroundTheory.Automorphic.Adele2.mixedFourier2_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:29:39.626413+00:00
-- url     : https://prove2.me/submissions/0759e809-b12a-4504-bde6-1711ce40d558

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceLatticePoisson
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_SummableNormIffAndTsumEqCoset2
import Theorems.Thm_GroundTheory_Automorphic_Adele2_mixedPairing2_eq_inner
import Theorems.Thm_GroundTheory_Automorphic_Adele2_measurePreserving_toEuclid2

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
theorem _root_.solution (f : (Fin 2 → mixedSpace K) → ℂ) (y : Fin 2 → mixedSpace K) :
    mixedFourier2 K f y = 𝓕 (f ∘ (toEuclid2 K).symm) (toEuclid2Conj K y) := by
  rw [mixedFourier2, Real.fourier_eq, ← (measurePreserving_toEuclid2 K).integral_comp
    (toEuclid2 K).toHomeomorph.measurableEmbedding]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp [mixedPairing2_eq_inner]
end GroundTheory.Automorphic.Adele2
