-- Prove2me | solution 1 for GroundTheory.Arith.Toric.exists_dual_neg_of_not_mem_hull_finset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:59:50.01563+00:00
-- url     : https://prove2.me/submissions/d2dfe224-f823-4eb1-8152-bfc793874904

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_ExistsDualNegOfNotMemHullFinset
import Theorems.Thm_GroundTheory_Arith_Toric_exists_dual_neg_of_not_mem_hull

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
theorem _root_.solution (S : Finset V) {x : V}
    (hx : x ∉ hull 𝕜 (S : Set V)) : ∃ f : Dual 𝕜 V, (∀ y ∈ S, 0 ≤ f y) ∧ f x < 0 :=
  exists_dual_neg_of_not_mem_hull S id (by simpa using hx)
end GroundTheory.Arith.Toric
