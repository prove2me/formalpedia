-- Prove2me | solution 1 for GroundTheory.Global.mixedFourierSchwartz_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:41:01.795974+00:00
-- url     : https://prove2.me/submissions/43558eb3-28da-4261-ad4b-a87d63a6bec3

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TracePairing
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceFourier
import Theorems.Thm_GroundTheory_Global_mixedFourier_eq

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
theorem _root_.solution (f : 𝓢(mixedSpace K, E)) :
    ⇑(mixedFourierSchwartz K f) = mixedFourier K f := by
  funext y
  rw [mixedFourier_eq]
  rfl
end GroundTheory.Global
