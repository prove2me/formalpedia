-- Prove2me | solution 1 for GroundTheory.Arith.Toric.mem_iff_forall_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:42:42.833614+00:00
-- url     : https://prove2.me/submissions/f3746753-2eee-4055-9b1f-5ad2f687006c

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_ExistsDualNegOfNotMemHullFinset
import Theorems.Thm_GroundTheory_Arith_Toric_exists_dual_neg_of_not_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Toric
open Module PointedCone
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {V W : Type*} [AddCommGroup V] [Module 𝕜 V] [AddCommGroup W] [Module 𝕜 W]
namespace GroundTheory.Arith.Toric
theorem _root_.solution {C : PointedCone 𝕜 V} (hC : C.FG) {x : V} :
    x ∈ C ↔ ∀ f : Dual 𝕜 V, (∀ y ∈ C, 0 ≤ f y) → 0 ≤ f x := by
  refine ⟨fun hx f hf => hf x hx, fun h => ?_⟩
  by_contra hx
  obtain ⟨f, hf, hfx⟩ := exists_dual_neg_of_not_mem hC hx
  exact (h f hf).not_gt hfx
end GroundTheory.Arith.Toric
