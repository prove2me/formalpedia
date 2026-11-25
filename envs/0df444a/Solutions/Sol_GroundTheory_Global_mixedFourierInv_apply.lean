-- Prove2me | solution 1 for GroundTheory.Global.mixedFourierInv_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:09:47.445796+00:00
-- url     : https://prove2.me/submissions/770f38a1-0db9-4a18-b875-dee02550aa9e

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TracePairing
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceFourier
import Theorems.Thm_GroundTheory_Global_mixedTraceForm_comm


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
    mixedFourierInv K f x = ∫ y, 𝐞 (mixedTraceForm K x y) • f y ∂selfDualMeasure K := by
  simp only [mixedFourierInv, VectorFourier.fourierIntegral, LinearMap.neg_apply, neg_neg,
    mixedTraceForm_comm K _ x]
end GroundTheory.Global
