-- Prove2me | solution 1 for GlobalTheory.succMin_map_linearIsometry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:35:58.214047+00:00
-- url     : https://prove2.me/submissions/8920a097-9fab-4eef-8b93-d7b88b01635b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Submodule
open scoped Pointwise
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {L L' : Submodule ℤ E} {i j : ℕ} {r : ℝ}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
namespace GlobalTheory
theorem _root_.solution (f : E →ₗᵢ[ℝ] F) (L : Submodule ℤ E) (i : ℕ) :
    succMin (L.map (f.toLinearMap.restrictScalars ℤ)) i = succMin L i :=
  succMinOf_image f.toLinearMap f.injective (fun x _ => f.norm_map x)
end GlobalTheory
