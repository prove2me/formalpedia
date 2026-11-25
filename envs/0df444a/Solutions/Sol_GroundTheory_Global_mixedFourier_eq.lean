-- Prove2me | solution 1 for GroundTheory.Global.mixedFourier_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:34:26.666219+00:00
-- url     : https://prove2.me/submissions/7eb15f2b-528a-4e58-8ad1-40b899cf5a0d

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TracePairing
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceFourier
import Theorems.Thm_GroundTheory_Global_measurePreserving_mixedToEuclidean
import Theorems.Thm_GroundTheory_Global_mixedTraceForm_eq_inner
import Theorems.Thm_GroundTheory_Global_mixedFourier_apply

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
namespace GroundTheory.Global
theorem _root_.solution (f : mixedSpace K → E) (y : mixedSpace K) :
    mixedFourier K f y = 𝓕 (f ∘ (mixedToEuclidean K).symm) (mixedToEuclideanConj K y) := by
  rw [mixedFourier_apply, Real.fourier_eq, ← (measurePreserving_mixedToEuclidean K).integral_comp
    (mixedToEuclidean K).toHomeomorph.measurableEmbedding]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [mixedTraceForm_eq_inner]
end GroundTheory.Global
