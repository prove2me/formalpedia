-- Prove2me | solution 1 for GroundTheory.Global.mixedFourierInv_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:37:13.350918+00:00
-- url     : https://prove2.me/submissions/bae0a5ba-2f50-40b1-965d-665a55063474

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TracePairing
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceFourier
import Theorems.Thm_GroundTheory_Global_measurePreserving_mixedToEuclideanConj
import Theorems.Thm_GroundTheory_Global_mixedTraceForm_eq_inner
import Theorems.Thm_GroundTheory_Global_mixedFourierInv_apply

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
theorem _root_.solution (f : mixedSpace K → E) (x : mixedSpace K) :
    mixedFourierInv K f x = 𝓕⁻ (f ∘ (mixedToEuclideanConj K).symm) (mixedToEuclidean K x) := by
  rw [mixedFourierInv_apply, Real.fourierInv_eq, ← (measurePreserving_mixedToEuclideanConj K).integral_comp
    (mixedToEuclideanConj K).toHomeomorph.measurableEmbedding]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp [mixedTraceForm_eq_inner, real_inner_comm]
end GroundTheory.Global
