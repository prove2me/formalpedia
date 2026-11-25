-- Prove2me | solution 1 for GlobalTheory.DominatesStalk.comap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:48:46.895477+00:00
-- url     : https://prove2.me/submissions/e69e75f8-dbe9-4dc8-a5ac-c0d31279c76d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsValuationSubringDominatingSubring
import Theorems.Thm_GlobalTheory_functionFieldMap_algebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
noncomputable section
open GlobalTheory
variable {X X' S : Scheme.{u}} [IsIntegral X] [IsIntegral X']
variable {W : ValuationSubring X.functionField} {x : X}
namespace GlobalTheory
namespace DominatesStalk
theorem _root_.solution (h : DominatesStalk W x) (f : X ⟶ X') [IsDominant f] :
    DominatesStalk (W.comap (functionFieldMap f)) (f x) := by
  refine ⟨fun a ↦ ?_, fun a ha ↦ ?_⟩
  · rw [ValuationSubring.mem_comap, functionFieldMap_algebraMap]
    exact h.1 _
  · have := h.2 _ (map_nonunit (f.stalkMap x).hom a ha)
    rw [← functionFieldMap_algebraMap] at this
    rw [ValuationSubring.mem_nonunits_iff_or] at this ⊢
    rwa [ValuationSubring.mem_comap, map_inv₀, ← map_eq_zero (functionFieldMap f)]
end DominatesStalk
end GlobalTheory
