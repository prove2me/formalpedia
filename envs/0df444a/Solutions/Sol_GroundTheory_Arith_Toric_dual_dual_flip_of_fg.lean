-- Prove2me | solution 1 for GroundTheory.Arith.Toric.dual_dual_flip_of_fg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:11:53.210638+00:00
-- url     : https://prove2.me/submissions/eab2da9e-8870-4278-be53-27775d3bc383

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
variable {M N : Type*} [AddCommGroup M] [Module 𝕜 M] [AddCommGroup N] [Module 𝕜 N]
namespace GroundTheory.Arith.Toric
theorem _root_.solution (p : M →ₗ[𝕜] N →ₗ[𝕜] 𝕜) (hp : Function.Surjective p)
    {C : PointedCone 𝕜 N} (hC : C.FG) : dual p (dual p.flip (C : Set N)) = C := by
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · by_contra hxC
    obtain ⟨f, hf, hfx⟩ := exists_dual_neg_of_not_mem hC hxC
    obtain ⟨m, rfl⟩ := hp f
    have hm : m ∈ dual p.flip (C : Set N) := fun y hy => by simpa using hf y hy
    exact (hx hm).not_gt hfx
  · intro m hm
    simpa using hm hx
end GroundTheory.Arith.Toric
