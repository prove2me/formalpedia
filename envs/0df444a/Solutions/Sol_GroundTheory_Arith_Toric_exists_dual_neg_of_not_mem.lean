-- Prove2me | solution 1 for GroundTheory.Arith.Toric.exists_dual_neg_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:05:53.392008+00:00
-- url     : https://prove2.me/submissions/d41e057f-f4d3-49b6-b878-80959868d34c

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_ExistsDualNegOfNotMemHullFinset
import Theorems.Thm_GroundTheory_Arith_Toric_nonneg_of_mem_hull
import Theorems.Thm_GroundTheory_Arith_Toric_exists_dual_neg_of_not_mem_hull_finset

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
theorem _root_.solution {C : PointedCone 𝕜 V} (hC : C.FG) {x : V} (hx : x ∉ C) :
    ∃ f : Dual 𝕜 V, (∀ y ∈ C, 0 ≤ f y) ∧ f x < 0 := by
  obtain ⟨S, rfl⟩ := hC
  obtain ⟨f, hf, hfx⟩ := exists_dual_neg_of_not_mem_hull_finset S hx
  exact ⟨f, fun y hy => nonneg_of_mem_hull hf hy, hfx⟩
end GroundTheory.Arith.Toric
